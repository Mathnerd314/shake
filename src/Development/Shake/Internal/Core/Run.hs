{-# LANGUAGE RecordWildCards, GeneralizedNewtypeDeriving, DeriveFunctor, ScopedTypeVariables, PatternGuards #-}
{-# LANGUAGE ExistentialQuantification, MultiParamTypeClasses, ConstraintKinds, ViewPatterns, TupleSections #-}

module Development.Shake.Internal.Core.Run(
    run', actionOnException, actionFinally, applyKeyValue, traced, getShakeOptions, getProgress,
    trackUse, trackChange, trackAllow,
    getVerbosity, putLoud, putNormal, putQuiet, withVerbosity, quietly,
    Resource, newResource, withResource, withResources, newThrottle,
    newCache,
    unsafeExtraThread,
    parallel,
    orderOnlyAction,
    -- Internal stuff
    runAfter,
    ) where

import Control.Exception.Extra
import Control.Applicative
import Data.Tuple.Extra
import Control.Concurrent.Extra
import Control.Monad.Extra
import Control.Monad.IO.Class
import Data.Typeable.Extra
import Control.Monad.Trans.Writer.Strict
import Data.Dynamic
import General.Binary
import Data.Function
import Data.Either.Extra
import Data.List.Extra
import qualified Data.HashMap.Strict as Map
import Data.Maybe
import Data.IORef
import System.IO.Extra
import System.Time.Extra
import Numeric.Extra

import Development.Shake.Classes
import Development.Shake.Internal.Core.Action
import Development.Shake.Internal.Core.Pool
import Development.Shake.Internal.Core.Database
import Development.Shake.Internal.Core.Rendezvous
import Development.Shake.Internal.Core.Monad
import Development.Shake.Internal.Resource
import Development.Shake.Internal.Profile
import Development.Shake.Internal.Types
import Development.Shake.Internal.Errors
import Development.Shake.Internal.Special
import General.Timing

import Data.Monoid

import General.Extra
import General.Cleanup
import Prelude

---------------------------------------------------------------------
-- MAKE

-- | Internal main function (not exported publicly)
run' :: ShakeOptions -> [ActionP k ()] -> BuildKey k -> IO ()
run' opts@ShakeOptions{..} actions ruleinfo = do
    outputLocked <- do
        lock <- newLock
        return $ \v msg -> withLock lock $ shakeOutput v msg

    let diagnostic = if shakeVerbosity >= Diagnostic then outputLocked Diagnostic . ("% "++) else const $ return ()
    let output v = outputLocked v . abbreviate shakeAbbreviations
    diagnostic "Starting run"

    except <- newIORef (Nothing :: Maybe (String, ShakeException))
    let raiseError err
            | not shakeStaunch = throwIO err
            | otherwise = do
                let named = abbreviate shakeAbbreviations . shakeExceptionTarget
                atomicModifyIORef except $ \v -> (Just $ fromMaybe (named err, err) v, ())
                -- no need to print exceptions here, they get printed when they are wrapped

    lint <- if shakeLint == LintNothing then return $ const $ return () else do
        dir <- getCurrentDirectory
        return $ \msg -> do
            diagnostic msg
            now <- getCurrentDirectory
            when (dir /= now) $ errorStructured
                "Lint checking error - current directory has changed"
                [("When", Just msg)
                ,("Wanted",Just dir)
                ,("Got",Just now)]
                ""
    diagnostic "Starting run 2"

    after <- newIORef []
    absent <- newIORef []
    withCleanup $ \cleanup -> do
        _ <- addCleanup cleanup $ do
            when shakeTimings printTimings
            resetTimings -- so we don't leak memory
        withNumCapabilities shakeThreads $ do
            diagnostic "Starting run 3"
            withDatabase opts diagnostic $ \database -> do
                wait <- newBarrier
                let getProgress = do
                        failure <- fmap fst <$> readIORef except
                        stats <- progress database
                        return stats{isFailure=failure}
                tid <- flip forkFinally (const $ signalBarrier wait ()) $
                    shakeProgress getProgress
                _ <- addCleanup cleanup $ do
                    killThread tid
                    void $ timeout 1000000 $ waitBarrier wait

                addTiming "Running rules"
                runPool (shakeThreads == 1) shakeThreads $ \pool -> do
                    let s0 = Global database pool cleanup start (rules rs) (userrules rs) output opts diagnostic lint after absent getProgress
                    let s1 = Local emptyStack shakeVerbosity Nothing mempty 0 [] [] []
                    forM_ actions $ \act ->
                        addPool pool $ runAction s0 s1 act $ \x -> case x of
                            Left e -> raiseError =<< shakeException s0 (return ["Top-level action/want"]) e
                            Right x -> return x
                maybe (return ()) (throwIO . snd) =<< readIORef except
                assertFinishedDatabase database

                let putWhen lvl msg = when (shakeVerbosity >= lvl) $ output lvl msg

                when (null actions) $
                    putWhen Normal "Warning: No want/action statements, nothing to do"

                when (basicLint shakeLint) $ do
                    addTiming "Lint checking"
                    absent' <- readIORef absent
                    checkValid database absent' $ \ks -> do
                        bad <- newIORef []
                        runPool (shakeThreads == 1) shakeThreads $ \pool -> do
                            let opts2 = opts{shakeRunCommands=RunMinimal}
                            let s0 = Global database pool cleanup start (rules rs) (userrules rs) output opts2 diagnostic lint after absent getProgress
                            forM_ ks $ \(i,(key,v)) -> do
                                    let reply = undefined
--     -- Do not use a forM here as you use too much stack space
--     bad <- (\f -> foldM f [] status) $ \seen (i,v) -> case v of
--         (key, Ready Result{..}) -> do
--             good <- check key result
--             diagnostic $ return $ "Checking if " ++ show key ++ " is " ++ show result ++ ", " ++ if isNothing good then "passed" else "FAILED"
--             return $ [(key, result, now) | not $ specialAlwaysRebuilds result, Just now <- [good]] ++ seen
--         _ -> return seen
--                                         reply (Error e) = raiseError =<< shakeException s0 (return ["Lint-checking"]) e
--                                         reply (Ready r) = do
--                                             let now = built r == changed r
--                                             diagnostic $ "Checking if " ++ show key ++ " is " ++ show (result ro) ++ ", " ++ if now then "passed" else "FAILED"
--                                             whenJust now $ \now -> modifyIORef' bad ((key, result ro, now):)
                                    runKey_
                                        s0 i key (Just $ resultStore ro) False
                                        emptyStack
                                        (incStep $ built $ resultStore ro)
                                        reply
                        maybe (return ()) (throwIO . snd) =<< readIORef except
                        readIORef bad
                    putWhen Loud "Lint checking succeeded"
                when (shakeReport /= []) $ do
                    addTiming "Profile report"
                    report <- toReport database
                    forM_ shakeReport $ \file -> do
                        putWhen Normal $ "Writing report to " ++ file
                        writeProfile file report
                when (shakeLiveFiles /= []) $ do
                    addTiming "Listing live"
                    -- TODO: get working
                    live <- listLive database
                    let liveFiles = [show k | k <- live, specialIsFileKey $ typeKey k]
                    forM_ shakeLiveFiles $ \file -> do
                        putWhen Normal $ "Writing live list to " ++ file
                        (if file == "-" then putStr else writeFile file) $ unlines liveFiles
            sequence_ . reverse =<< readIORef after

lineBuffering :: IO a -> IO a
lineBuffering act = do
    -- instead of withBuffering avoid two finally handlers and stack depth
    out <- hGetBuffering stdout
    err <- hGetBuffering stderr
    hSetBuffering stdout LineBuffering
    hSetBuffering stderr LineBuffering
    act `finally` do
        hSetBuffering stdout out
        hSetBuffering stderr err

-- | Whether to do basic lint checks
basicLint :: Lint -> Bool
basicLint = (/= LintNothing)

-- | Execute a list of keys, adding them as dependencies, returning the associated values.
--   The rules will be run in parallel, subject to the thread limit.
applyKeyValue :: [k] -> ActionP k [LiveResult]
applyKeyValue [] = return []
applyKeyValue ks = do
    Global{..} <- Action getRO
    stack <- Action $ getsRW localStack
    (dep, vs) <- traced' "apply" $ Action $ captureRAW $ \cont -> do
        (dep, w) <- build globalPool globalDatabase globalRun stack ks
        case w of
          Now v -> cont (dep,v)
          Wait w -> afterWaiting w (addPool HighPriority pool . cont . (dep,))
    Action $ modifyRW $ \s -> s{localDepends=dep <> localDepends s}
    return vs

-- | Turn a normal exception into a ShakeException, giving it a stack and printing it out if in staunch mode.
--   If the exception is already a ShakeException (e.g. it's a child of ours who failed and we are rethrowing)
--   then do nothing with it.
shakeException :: Global k -> IO [String] -> SomeException -> IO ShakeException
shakeException Global{globalOptions=ShakeOptions{..},..} stk e@(SomeException inner) = case cast inner of
    Just e@ShakeException{} -> return e
    Nothing -> do
        stk <- stk
        e <- return $ ShakeException (last $ "Unknown call stack" : stk) stk e
        when (shakeStaunch && shakeVerbosity >= Quiet) $
            globalOutput Quiet $ show e ++ "Continuing due to staunch mode"
        return e

---------------------------------------------------------------------
-- TRACKING

-- | Track that a file has been read by the action preceeding it.
trackUse :: key -> ActionP key ()
trackUse key = do
    Global{..} <- Action getRO
    l@Local{..} <- Action getRW
    when (basicLint $ shakeLint globalOptions) $ do
        let k = newKey key
        deps <- liftIO $ listDepends globalDatabase localDepends
        let top = topStack localStack
        if top == Just k then
            return () -- condition 1
        else if k `elem` deps then
            return () -- condition 2
        else if any ($ k) localTrackAllows then
            return () -- condition 3
        else
            Action $ putRW l{localTrackUsed = k : localTrackUsed} -- condition 4

Track that a key has been changed by the action; the key is either building, given permission with trackAllow, or untracked and not in the database
Allow any matching key to violate the tracking rules.

-- | Check that no values were used but not depended upon or built after being used
trackCheckUsed :: ActionP key ()
trackCheckUsed = do
    Global{..} <- Action getRO
    Local{..} <- Action getRW
    when (basicLint $ shakeLint globalOptions) $ liftIO $ do
        deps <- listDepends globalDatabase localDepends

        -- check 3a
        bad <- return $ localTrackUsed \\ deps
        unless (null bad) $ do
            let n = length bad
            errorStructured
                ("Lint checking error - " ++ (if n == 1 then "value was" else show n ++ " values were") ++ " used but not depended upon")
                [("Used", Just $ show x) | x <- bad]
                ""

        -- check 3b
        bad <- flip filterM localTrackUsed $ \k -> (not . null) <$> lookupDependencies globalDatabase k
        unless (null bad) $ do
            let n = length bad
            errorStructured
                ("Lint checking error - " ++ (if n == 1 then "value was" else show n ++ " values were") ++ " depended upon after being used")
                [("Used", Just $ show x) | x <- bad]
                ""


-- | Track that a key has been changed by the action preceeding it.
trackChange :: key -> ActionP key ()
-- * The build result does not depend on the previous external state
--   If an external datum is modified, then every rule reading that datum must execute afterwards.

-- One of the following must be true:
-- 1) you are the one building this key (e.g. key == topStack)
-- 2) someone explicitly gave you permission with trackAllow
-- 3) this file is never known to the build system, at the end it is not in the database
trackChange key = do
    let k = newKey key
    Global{..} <- Action getRO
    Local{..} <- Action getRW
    when (basicLint $ shakeLint globalOptions) $ liftIO $ do
        let top = topStack localStack
        if top == Just k then
            return () -- condition 1
         else if any ($ k) localTrackAllows then
            return () -- condition 2
         else
            -- condition 3
            atomicModifyIORef globalTrackAbsent $ \ks -> ((fromMaybe k top, k):ks, ())


-- | Allow any matching key to violate the tracking rules.
trackAllow :: (key -> Bool) -> ActionP key ()
trackAllow test = do
    Global{..} <- Action getRO
    when (basicLint $ shakeLint globalOptions) $ Action $ modifyRW $ \s -> s{localTrackAllows = f : localTrackAllows s}
    where

---------------------------------------------------------------------
-- RESOURCES

-- | Run an action which uses part of a finite resource. For more details see 'Resource'.
--   Note that if you call 'withResource' while a resource is held, and the new resource is not
--   available, all resources held will be released while waiting for the new resource, and
--   re-acquired after; this may cause undesirable behavior. Also note that 'need' and 'apply'
--   will similarly release all resources while executing a dependency, and re-acquire them later.
withResource :: Resource -> Int -> ActionP k a -> ActionP k a
withResource r i act = do
    Global{..} <- Action getRO
    traced' (show r ++ " waiting to acquire " ++ show i) $
      Action $ captureRAW $ \continue -> acquireResource r globalPool i $ continue $ Right ()
    res <- act
    liftIO $ releaseResource r globalPool i
    liftIO $ globalDiagnostic $ show r ++ " released " ++ show i
    Action $ either throwRAW return res

-- | Run an action which uses part of several finite resources. Acquires the resources in a stable
--   order, to prevent deadlock. If all rules requiring more than one resource acquire those
--   resources with a single call to 'withResources', resources will not deadlock.
withResources :: [(Resource, Int)] -> ActionP k a -> ActionP k a
withResources res act
    | (r,i):_ <- filter ((< 0) . snd) res = error $ "You cannot acquire a negative quantity of " ++ show r ++ ", requested " ++ show i
    | otherwise = f $ groupBy ((==) `on` fst) $ sortBy (compare `on` fst) res
    where
        f [] = act
        f (r:rs) = withResource (fst $ head r) (sum $ map snd r) $ f rs


-- | Given an action on a key, produce a cached version that will execute the action at most once per key per Shake invocation.
--   Using the cached result will still result include any dependencies that the action requires.
--   Each call to 'newCache' creates a separate cache that is independent of all other calls to 'newCache'.
--
--   This function is useful when creating files that store intermediate values,
--   to avoid the overhead of repeatedly reading from disk, particularly if the file requires expensive parsing.
--   As an example:
--
-- @
-- digits \<- 'newCache' $ \\file -> do
--     src \<- readFile\' file
--     return $ length $ filter isDigit src
-- \"*.digits\" 'Development.Shake.%>' \\x -> do
--     v1 \<- digits ('dropExtension' x)
--     v2 \<- digits ('dropExtension' x)
--     'Development.Shake.writeFile'' x $ show (v1,v2)
-- @
--
--   To create the result @MyFile.txt.digits@ the file @MyFile.txt@ will be read and counted, but only at most
--   once per execution.
newCache :: (Eq k, Hashable k, MonadIO m) => (k -> ActionP k v) -> m (k -> ActionP k v)
newCache act = liftIO $ do
    var {- :: Var (Map k (Fence (Either SomeException ([Depends],v)))) -} <- newVar Map.empty
    return $ \key ->
        join $ liftIO $ modifyVar var $ \mp -> case Map.lookup key mp of
            Just bar -> return $ (,) mp $ do
                res <- liftIO $ testFence bar
                (res,offset) <- case res of
                    Just res -> return (res, 0)
                    Nothing -> do
                        pool <- Action $ getsRO globalPool
                        offset <- liftIO offsetTime
                        Action $ captureRAW $ \k -> waitFence bar $ \v ->
                            addPool pool $ do offset <- liftIO offset; k $ Right (v,offset)
                case res of
                    Left err -> ActionP k $ throwRAW err
                    Right (deps,v) -> do
                        Action $ modifyRW $ \s -> s{localDepends = deps <> localDepends s, localDiscount = localDiscount s + offset}
                        return v
            Nothing -> do
                bar <- newFence
                return $ (,) (Map.insert key bar mp) $ do
                    pre <- Action $ getsRW localDepends
                    res <- Action $ tryRAW $ fromAction $ act key
                    case res of
                        Left err -> do
                            liftIO $ signalFence bar $ Left err
                            Action $ throwRAW err
                        Right v -> do
                            post <- Action $ getsRW localDepends
                            let deps = subtractDepends pre post
                            liftIO $ signalFence bar $ Right (deps, v)
                            return v

-- | Temporarily release this thread's resource, allowing other threads to run.
--   Typically used for actions that execute on remote machines using barely any local CPU resources.
--   Unsafe as it allows the 'shakeThreads' limit to be exceeded, although
--   the number of threads that are not within an unsafeExtraThread section will still be at most shakeThreads.
--   Calling dependencies (e.g. 'need') from within unsafeExtraThread will still use a thread.
unsafeExtraThread :: ActionP k a -> ActionP k a
unsafeExtraThread act = Action $ do
    Global{..} <- getRO
    res <- tryRAW $ fromAction $ blockApply "Within unsafeExtraThread" act
    liftIO stop
    captureRAW $ \continue -> (if isLeft res then addPoolHighPriority else addPoolMediumPriority) globalPool $ continue res


-- | Execute a list of actions in parallel. In most cases 'need' will be more appropriate to benefit from parallelism.
--   'need' takes a single database lock and uses as many cached values as possible, while 'parallel' will have to lock many times
--   and must spawn a thread regardless of caching.
parallel :: [ActionP k a] -> ActionP k [a]
parallel [] = return []
parallel [x] = fmap return x
parallel acts = Action $ do
    global@Global{..} <- getRO
    local <- getRW
    -- number of items still to complete, or Nothing for has completed (by either failure or completion)
    todo :: Var (Maybe Int) <- liftIO $ newVar $ Just $ length acts
    -- a list of refs where the results go
    results :: [IORef (Maybe (Either SomeException a))] <- liftIO $ replicateM (length acts) $ newIORef Nothing

    captureRAW $ \continue -> do
        let resume = do
                res <- liftIO $ sequence . catMaybes <$> mapM readIORef results
                continue res

        liftIO $ forM_ (zip acts results) $ \(act, result) -> do
            let act2 = ifM (liftIO $ isJust <$> readVar todo) act (fail "")
            addPoolMediumPriority globalPool $ runAction global local act2 $ \res -> do
                writeIORef result $ Just res
                modifyVar_ todo $ \v -> case v of
                    Nothing -> return Nothing
                    Just i | i == 1 || isLeft res -> do resume; return Nothing
                    Just i -> return $ Just $ i - 1
