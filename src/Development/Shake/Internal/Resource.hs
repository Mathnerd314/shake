{-# LANGUAGE RecordWildCards, ViewPatterns, DeriveDataTypeable, DeriveGeneric #-}

module Development.Shake.Internal.Resource(
    Resource, newResourceIO, newThrottleIO, acquireResource, releaseResource
    ) where

import Data.Function
import System.IO.Unsafe
import Control.Concurrent.Extra
import Control.Exception.Extra
import Data.Tuple.Extra
import Control.Monad
import General.Bilist
import Development.Shake.Internal.Core.Pool
import System.Time.Extra
import Data.Monoid
import Prelude
import Control.Monad
import Data.Typeable
import GHC.Generics
import qualified Data.HashMap.Strict as Map
import System.Random

---------------------------------------------------------------------
-- UNFAIR/RANDOM QUEUE

-- Monad for non-deterministic (but otherwise pure) computations
type NonDet a = IO a

-- | A FIFO queue for priority actions plus low-priority pending actions.
--   Left = deterministic FIFO list, Right = non-deterministic tree
data Queue a = Queue (Bilist a) (Either (Bilist a) (Tree a))

newQueue :: Bool -> Queue a
newQueue deterministic = Queue mempty $ if deterministic then Left mempty else Right emptyTree

enqueuePriority :: a -> Queue a -> Queue a
enqueuePriority x (Queue p t) = Queue (x `cons` p) t

enqueue :: a -> Queue a -> Queue a
enqueue x (Queue p (Left xs)) = Queue p $ Left $ xs `snoc` x
enqueue x (Queue p (Right t)) = Queue p $ Right $ insertTree x t

dequeue :: Queue a -> NonDet (Maybe (a, Queue a))
dequeue (Queue pl t) = case uncons pl of
  Just (p,ps) -> return $ Just (p, Queue ps t)
  Nothing -> case t of
     Left bl -> return $ case (uncons bl) of
        Just (x,xs) -> Just (x, Queue [] $ Left xs)
        Nothing -> Nothing
     Right t -> do
        bs <- randomIO
        return $ case removeTree bs t of
            Nothing -> Nothing
            Just (x,t) -> Just (x, Queue [] $ Right t)

-- | A tree with fast removal. Nodes are stored at indicies 0..n-1. TODO: use array instead?
data Tree a = Tree {-# UNPACK #-} !Int (Map.HashMap Int a)

emptyTree :: Tree a
emptyTree = Tree 0 Map.empty

insertTree :: a -> Tree a -> Tree a
insertTree x (Tree n mp) = Tree (n+1) $ Map.insert n x mp

-- Remove an item, put the n-1 item to go in it's place
removeTree :: Int -> Tree a -> Maybe (a, Tree a)
removeTree rnd (Tree n mp)
        | n == 0 = Nothing
        | n == 1 = Just (mp Map.! 0, emptyTree)
        | i == n-1 = Just (mp Map.! i, Tree (n-1) $ Map.delete i mp)
        | otherwise = Just (mp Map.! i, Tree (n-1) $ Map.insert i (mp Map.! (n-1)) $ Map.delete (n-1) mp)
    where
        i = abs rnd `mod` n

---------------------------------------------------------------------
-- RESOURCES

{-# NOINLINE resourceIds #-}
resourceIds :: Var Int
resourceIds = unsafePerformIO $ newVar 0

resourceId :: IO Int
resourceId = modifyVar resourceIds $ \i -> let j = i + 1 in j `seq` return (j, j)


-- | A type representing an external resource which the build system should respect. There
--   are two ways to create 'Resource's in Shake:
--
-- * 'Development.Shake.newResource' creates a finite resource, stopping too many actions running
--   simultaneously.
--
-- * 'Development.Shake.newThrottle' creates a throttled resource, stopping too many actions running
--   over a short time period.
--
--   These resources are used with 'Development.Shake.withResource' when defining rules. Typically only
--   IO-intensive system commands (such as 'Development.Shake.cmd') should be run inside 'Development.Shake.withResource',
--   as 'Development.Shake.need' automatically uses a CPU thread resource.
--
--   Be careful that the actions run within 'Development.Shake.withResource' do not themselves require further
--   copies of the resource, or you may get a \"thread blocked indefinitely in an MVar operation\" exception.
--   If an action requires multiple resources, use 'Development.Shake.withResources' to avoid deadlock.
data Resource = Resource
    {resourceOrd :: Int
        -- ^ Key used for Eq/Ord operations. To make withResources work, we require newResourceIO < newThrottleIO
    ,resourceShow :: IO String
        -- ^ String used for Show
    ,acquireResource :: Pool -> Int -> IO () -> IO ()
        -- ^ Acquire the resource and call the function.
    ,releaseResource :: Pool -> Int -> IO ()
        -- ^ You should only ever releaseResource that you obtained with acquireResource.
    }

instance Show Resource where show = resourceShow
instance Eq Resource where (==) = (==) `on` resourceOrd
instance Ord Resource where compare = compare `on` resourceOrd

worker :: Pool -> IO ()
worker todo = now >> worker pool

data Priority = LowPriority -- ^ Low priority is suitable for new tasks that are just starting. Currently equivalent to Medium.
              | MediumPriority -- ^ Medium priority is suitable for tasks that are resuming running after a pause.
              | HighPriority -- ^ High priority is suitable for tasks that have detected failure and are resuming to propagate that failure.
  deriving (Eq,Ord,Show,Read,Typeable,Generic,Enum,Bounded)

addQueue HighPriority = enqueuePriority
addQueue _ = enqueue

---------------------------------------------------------------------
-- FINITE RESOURCES

data Finite = Finite
    {finiteAvailable :: {-# UNPACK #-} !Int
        -- ^ number of currently available resources
    ,finiteLimit :: {-# UNPACK #-} !Int -- ^ supplied resource limit, = finiteAvailable + acquired resources
    ,finiteMin :: {-# UNPACK #-} !Int -- ^ low water mark of available resources (accounting only)
    ,finiteSum :: {-# UNPACK #-} !Int -- ^ number of resources we have been through (accounting only)
    ,finiteWaiting :: Queue (Int, IO ())
        -- ^ queue of people with how much they want and the action when it is allocated to them
    }

-- | A version of 'Development.Shake.newResource' that runs in IO, and can be called before calling 'Development.Shake.shake'.
--   Most people should use 'Development.Shake.newResource' instead.
newResourceIO :: String -> Int -> IO Resource
newResourceIO name mx = do
    when (mx < 0) $
        errorIO $ "You cannot create a resource named " ++ name ++ " with a negative quantity, you used " ++ show mx
    key <- resourceId
    var <- newVar $ Finite mx mx 0 0 mempty
    return $ Resource (negate key) shw (acquire var) (release var)
    where
        shw var = do
          Finite{..} <- readVar var
          return $ "Resource " ++ name ++ " ("
              ++ show finiteAvailable ++ " available, "
              ++ show finiteLimit ++ " max, used"
              ++ show (finiteLimit - finiteMin) ++ " max &"
              ++ show finiteSum ++ " total)"

        acquire :: Var Finite -> Pool -> Int -> IO () -> IO ()
        acquire var pool want continue
            | want < 0 = errorIO $ "You cannot acquire a negative quantity of " ++ shw ++ ", requested " ++ show want
            | want > mx = errorIO $ "You cannot acquire more than " ++ show mx ++ " of " ++ shw ++ ", requested " ++ show want
            | otherwise = join  $ modifyVar var $ \x@Finite{..} -> return $
                if want <= finiteAvailable then
                    (x{ finiteAvailable = finiteAvailable - want
                      , finiteSum = finiteSum + want
                      , finiteMin = (finiteAvailable - want) `min` finiteMin}
                    , continue)
                else
                    (x{finiteWaiting = addQueue MediumPriority (want, continue) finiteWaiting}, return ())

        release :: Var Finite -> Pool -> Int -> IO ()
        release var pool i = join $ modifyVar var $ \x -> f x{finiteAvailable = finiteAvailable x + i}
            where
                f fin@Finite{..} = do
                  res <- dequeue finiteWaiting
                  case res of
                      Just ((wi,wa),ws)
                          | wi <= finiteAvailable -> do
                              (val,ret) <- f $ fin { finiteAvailable = finiteAvailable - wi, finiteWaiting = ws }
                              return (val, wa >> ret)
                      _ -> (fin, return ())

---------------------------------------------------------------------
-- THROTTLE RESOURCES


-- call a function after a certain delay
waiter :: Seconds -> IO () -> IO ()
waiter period act = void $ forkIO $ do
    sleep period
    act

-- Make sure the pool cannot run try until after you have finished with it
blockPool :: Pool -> IO (IO ())
blockPool pool = do
    bar <- newBarrier
    addPool MediumPriority pool $ do
        cancel <- increasePool pool
        waitBarrier bar
        cancel
    return $ signalBarrier bar ()


data Throttle
      -- | Some number of resources are available
    = ThrottleAvailable !Int
      -- | Some users are blocked (non-empty), plus an action to call once we go back to Available
    | ThrottleWaiting (IO ()) (Bilist (Int, IO ()))


-- | A version of 'Development.Shake.newThrottle' that runs in IO, and can be called before calling 'Development.Shake.shake'.
--   Most people should use 'Development.Shake.newThrottle' instead.
newThrottleIO :: String -> Int -> Double -> IO Resource
newThrottleIO name count period = do
    when (count < 0) $
        errorIO $ "You cannot create a throttle named " ++ name ++ " with a negative quantity, you used " ++ show count
    key <- resourceId
    var <- newVar $ ThrottleAvailable count
    return $ Resource key (shw var) (acquire var) (release var)
    where
        shw var = do
          t <- readVar var
          return $ "Throttle " ++ name ++ " ("
              ++ case t of
                    ThrottleAvailable i -> show i ++ " available)"
                    ThrottleWaiting _ _ -> "waiting)"


        acquire :: Var Throttle -> Pool -> Int -> IO () -> IO ()
        acquire var pool want continue
            | want < 0 = errorIO $ "You cannot acquire a negative quantity of " ++ shw ++ ", requested " ++ show want
            | want > count = errorIO $ "You cannot acquire more than " ++ show count ++ " of " ++ shw ++ ", requested " ++ show want
            | otherwise = join $ modifyVar var $ \x -> case x of
                ThrottleAvailable i
                    | i >= want -> return (ThrottleAvailable $ i - want, continue)
                    | otherwise -> do
                        stop <- blockPool pool
                        return (ThrottleWaiting stop $ (want - i, addPool MediumPriority pool continue) `cons` mempty, return ())
                ThrottleWaiting stop xs -> return (ThrottleWaiting stop $ xs `snoc` (want, addPool MediumPriority pool continue), return ())

        release :: Var Throttle -> Pool -> Int -> IO ()
        release var pool n = waiter period $ join $ modifyVar var $ \x -> return $ case x of
                ThrottleAvailable i -> (ThrottleAvailable $ i+n, return ())
                ThrottleWaiting stop xs -> f stop n xs
            where
                f stop i (uncons -> Just ((wi,wa),ws))
                    | i >= wi = second (wa >>) $ f stop (i-wi) ws
                    | otherwise = (ThrottleWaiting stop $ (wi-i,wa) `cons` ws, return ())
                f stop i _ = (ThrottleAvailable i, stop)
