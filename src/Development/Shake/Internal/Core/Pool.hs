
-- | Thread pool implementation.
module Development.Shake.Internal.Core.Pool(
    Pool, runPool, addPool
    ) where

import Control.Concurrent.Extra
import System.Time.Extra
import Control.Exception
import General.Timing
import qualified Data.HashSet as Set
import Development.Shake.Internal.Core.Monad(Capture)
import Control.DeepSeq

-- | Thread pool. It keeps a set of all active threads (the var), and a barrier to notify when finished.
data Pool = Pool
    {-# UNPACK #-} !(Var (Maybe (Set.HashSet ThreadId))) -- ^ Current state, 'Nothing' to say we are aborting.
    {-# UNPACK #-} !(Barrier (Maybe SomeException)) -- ^ Barrier for the final result, 'Just' to signal that we are aborting, 'Nothing' on success

-- | IMPORTANT: The var must be strict or we leak thread stacks
modifyVarStrict_ :: NFData a => Var a -> (a -> IO a) -> IO ()
modifyVarStrict_ m io = modifyVar_ m $ \a -> io a >>= evaluate . force

-- | Spawn a new thread for the given action and add it to the pool
addPool :: Pool -> IO () -> IO ()
addPool pool@(Pool var done) now = do
    let onVar act = modifyVarStrict_ var $ maybe (return Nothing) act
    onVar $ \s -> do
      t <- forkFinally now $ \res -> onVar $ \s -> do
          t <- myThreadId
          let threads = Set.delete t s
          case res of
              Left e -> do
                  mapM_ killThread $ Set.toList threads
                  signalBarrier done $ Just e
                  return Nothing
              Right _ -> do
                  if (Set.null $ threads)
                    then do
                      signalBarrier done Nothing
                      return Nothing
                    else return $ Just threads
      return $ Just $! Set.insert t s


-- | Run tasks in the pool.
--   If any thread throws an exception, all others will be killed, and the exception will be reraised.
runPool :: Capture Pool
runPool act = do
    s <- newVar $ Just $ Set.empty
    done <- newBarrier

    let cleanup = modifyVarStrict_ s $ \s -> do
            -- if someone kills our thread, make sure we kill our child threads
            case s of
                Just s -> mapM_ killThread s
                Nothing -> return ()
            return Nothing

    let ghc10793 = do
            -- if this thread dies because it is blocked on an MVar there's a chance we have
            -- a better error in the done barrier, and GHC raised the exception wrongly, see:
            -- https://ghc.haskell.org/trac/ghc/ticket/10793
            sleep 1 -- give it a little bit of time for the finally to run
                    -- no big deal, since the blocked indefinitely takes a while to fire anyway
            res <- waitBarrierMaybe done
            case res of
                Just (Just e) -> throwIO e
                _ -> throwIO BlockedIndefinitelyOnMVar
    handle (\BlockedIndefinitelyOnMVar -> ghc10793) $ flip onException cleanup $ do
        let pool = Pool s done
        addPool pool $ act pool
        res <- waitBarrier done
        case res of
            Just e -> throwIO e
            Nothing -> addTiming $ "Pool finished"
