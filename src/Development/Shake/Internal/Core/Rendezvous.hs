{-# LANGUAGE ExistentialQuantification, InstanceSigs, ScopedTypeVariables, LambdaCase #-}

module Development.Shake.Internal.Core.Rendezvous(
    Waiting, newWaiting, afterWaiting, runWaiting, showWaiting,
    Answer(..), Compute(..),
    rendezvous
    ) where

import Control.Monad
import Data.IORef.Extra
import Data.Primitive.Array
import Development.Shake.Internal.Errors
import Data.Typeable
import Control.Exception (assert)


-- | A type representing someone waiting for a result.
data Waiting a = Waiting (IORef [a -> IO ()])

contraMapWaiting :: (b -> a) -> Waiting a -> IO (Waiting b)
contraMapWaiting f w = Waiting <$> newIORef [runWaiting w . f]

showWaiting :: forall a. Typeable a => Waiting a -> IO String
showWaiting (Waiting a) = do
  ws <- readIORef a
  return $ "Waiting " ++ show (typeOf (undefined :: a)) ++ " <" ++ show (length ws) ++ " queued>"

runWaiting :: Waiting a -> a -> IO ()
runWaiting (Waiting ref) x = readIORef ref >>= mapM_ ($ x)

newWaiting :: IO (Waiting a)
newWaiting = Waiting <$> newIORef []

afterWaiting :: Waiting a -> (a -> IO ()) -> IO ()
afterWaiting (Waiting ref) act = modifyIORef' ref (act :)

-- | A result available immediately,
--   or a computation eventually producing a result
data Answer a
    = Now a
    | Wait (IO (Waiting a))

-- | A computation that either has an error making other computation moot,
--   a result available immediately,
--   or a computation producing a result that can be collected later.
data Compute a c
    = Abort a
    | Continue c
    | Later (Waiting (Compute a c))

data Partial a c = A a | B [c] | C [Either c (Waiting (Compute a c))] Int

rendezvous :: Monad m => [m (Compute a c)] -> m (Answer (Either a [c]))
rendezvous xs = do
    rs <- foldr f (return $ B []) xs
    pure $ case rs of
      A a -> Now $ Left a
      B bs -> assert (length bs == length xs) $ Now $ Right bs
      C cs later -> Wait $ do
          waiting <- newWaiting
          let n = length cs
          result <- newArray n $ err "rendezvous"
          todo <- newIORef later
          forM_ (zip [0..] cs) $ \(i,x) -> case x of
              Left c -> writeArray result i c
              Right w ->
                let waitOn w = afterWaiting w $ \v -> do
                      t <- readIORef todo
                      case v of
                          _ | t == 0 -> return () -- must have already aborted
                          Abort a -> do
                              writeIORef todo 0
                              runWaiting waiting $ Left a
                          Continue c -> do
                              writeArray result i c
                              writeIORef' todo $ t-1
                              when (t == 1) $ do
                                  rs <- unsafeFreezeArray result
                                  runWaiting waiting $ Right $ map (indexArray rs) [0..n-1]
                          Later w' -> waitOn w'
                in waitOn w
          return waiting
  where
    f :: Monad m => m (Compute a c) -> m (Partial a c) -> m (Partial a c)
    f act p = act >>= \case
        Abort a -> return $ A a
        c -> flip fmap p $ \p -> case (c,p) of
            (_,A a) -> A a
            (Continue c,B xs) -> B (c:xs)
            (Later l,B xs) -> C (Right l : map Left xs) 1
            (Continue c,C xs i) -> C (Left c:xs) i
            (Later l,C xs i) -> C (Right l : xs) (i+1)
