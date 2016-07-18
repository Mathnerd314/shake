{-# LANGUAGE RecordWildCards, ViewPatterns, DeriveDataTypeable, DeriveGeneric #-}

module Development.Shake.Internal.Resource(
    Resource, newResource, newThrottle, acquireResource, releaseResource
    ) where


import Control.Concurrent.Extra
import Control.Exception.Extra
import Control.Monad
import Control.Monad.IO.Class
import Data.Function
import Data.Monoid
import Data.Tuple.Extra
import Data.Typeable
import Development.Shake.Internal.Core.Pool
import GHC.Generics
import General.Bilist
import Prelude
import System.IO.Unsafe
import System.Random
import System.Time.Extra
import qualified Data.HashMap.Strict as Map
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

-- | Create a finite resource, given a name (for error messages) and a quantity of the resource that exists.
--   Shake will ensure that actions using the same finite resource do not execute in parallel.
--   As an example, only one set of calls to the Excel API can occur at one time, therefore
--   Excel is a finite resource of quantity 1. You can write:
--
-- @
-- 'Development.Shake.shake' 'Development.Shake.shakeOptions'{'Development.Shake.shakeThreads'=2} $ do
--    'Development.Shake.want' [\"a.xls\",\"b.xls\"]
--    excel <- 'Development.Shake.newResource' \"Excel\" 1
--    \"*.xls\" 'Development.Shake.%>' \\out ->
--        'Development.Shake.withResource' excel 1 $
--            'Development.Shake.cmd' \"excel\" out ...
-- @
--
--   Now the two calls to @excel@ will not happen in parallel.
--
--   As another example, calls to compilers are usually CPU bound but calls to linkers are usually
--   disk bound. Running 8 linkers will often cause an 8 CPU system to grid to a halt. We can limit
--   ourselves to 4 linkers with:
--
-- @
-- disk <- 'Development.Shake.newResource' \"Disk\" 4
-- 'Development.Shake.want' [show i 'Development.Shake.FilePath.<.>' \"exe\" | i <- [1..100]]
-- \"*.exe\" 'Development.Shake.%>' \\out ->
--     'Development.Shake.withResource' disk 1 $
--         'Development.Shake.cmd' \"ld -o\" [out] ...
-- \"*.o\" 'Development.Shake.%>' \\out ->
--     'Development.Shake.cmd' \"cl -o\" [out] ...
-- @
newResource :: (MonadIO m) => String -> Int -> m Resource
newResource name mx = liftIO $ do
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


-- | Create a throttled resource, given a name (for error messages) and a number of resources (the 'Int') that can be
--   used per time period (the 'Double' in seconds). Shake will ensure that actions using the same throttled resource
--   do not exceed the limits. As an example, let us assume that making more than 1 request every 5 seconds to
--   Google results in our client being blacklisted, we can write:
--
-- @
-- google <- 'Development.Shake.newThrottle' \"Google\" 1 5
-- \"*.url\" 'Development.Shake.%>' \\out -> do
--     'Development.Shake.withResource' google 1 $
--         'Development.Shake.cmd' \"wget\" [\"http:\/\/google.com?q=\" ++ 'Development.Shake.FilePath.takeBaseName' out] \"-O\" [out]
-- @
--
--   Now we will wait at least 5 seconds after querying Google before performing another query. If Google change the rules to
--   allow 12 requests per minute we can instead use @'Development.Shake.newThrottle' \"Google\" 12 60@, which would allow
--   greater parallelisation, and avoid throttling entirely if only a small number of requests are necessary.
--
--   In the original example we never make a fresh request until 5 seconds after the previous request has /completed/. If we instead
--   want to throttle requests since the previous request /started/ we can write:
--
-- @
-- google <- 'Development.Shake.newThrottle' \"Google\" 1 5
-- \"*.url\" 'Development.Shake.%>' \\out -> do
--     'Development.Shake.withResource' google 1 $ return ()
--     'Development.Shake.cmd' \"wget\" [\"http:\/\/google.com?q=\" ++ 'Development.Shake.FilePath.takeBaseName' out] \"-O\" [out]
-- @
--
--   However, the rule may not continue running immediately after 'Development.Shake.withResource' completes, so while
--   we will never exceed an average of 1 request every 5 seconds, we may end up running an unbounded number of
--   requests simultaneously. If this limitation causes a problem in practice it can be fixed.
newThrottle :: (MonadIO m) => String -> Int -> Double -> m Resource
newThrottle name count period = liftIO $ do
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

-- More resource types:
-- token bucket / leaky bucket: infrequent bursts of calls and a maximum average rate. The bucket size is 40 calls, with a "leak rate" of 2 calls per second that continually empties the bucket. If your app averages 2 calls per second, it will not overflow; if it is more, the bucket will fill up and eventually overflow.
--
-- Sliding window that is updated every few minutes. 480,000 calls can be made in a 24-hour period.
--
-- limit-remaining-reset (is this the current throttle?)
--
-- Hourly API usage is tracked from the start of one-hour to start of the next hour. If the API call rate limit is reached, you will receive an exception for each call until the start of the next hour (this can be up to 60 minutes). The exception message states: “The maximum number of hourly API invocations has been exceeded” (error number 207).
--
--
--     The algorithm and data structure I chose was straightforward.
--     I keep a timestamp log of requests in a Redis list data type which allows fast appending and trimming of elements.
-- As an example, I will use the table below to show the timestamps of five previous requests.
-- Requests ago 	1 	2 	3 	4 	5
-- Timestamp 	12:34:28 	12:34:26 	12:34:14 	12:33:37 	12:33:35
--
-- If I have two rules of 1 per second and 5 per minute, I grab the 1st and 5th timestamps representing the last request and 5 requests ago.
-- If the 1st timestamp is less than 1 second old the first rate limit rule will fail. Likewise if the 5th timestamp is less than 1 minute old the second rule fails.
-- At 12:34:31 the first timestamp is 3 seconds old, but the 5th timestamp is only 56 seconds old triggering the second rule. We could calculate we need to wait 4 seconds before trying again.
-- At 12:34:40 the first rule passes as it is 12 seconds old, the second rule also passes as it is now 65 seconds old.

-- GCRA
