{-# LANGUAGE RecordWildCards, GeneralizedNewtypeDeriving, DeriveFunctor, ScopedTypeVariables, PatternGuards #-}
{-# LANGUAGE ExistentialQuantification, MultiParamTypeClasses, ConstraintKinds, ViewPatterns #-}

module Development.Shake.Internal.Core.Run(
    run,
    Action, actionOnException, actionFinally, apply, apply1, traced, getShakeOptions, getProgress,
    trackUse, trackChange, trackAllow,
    getVerbosity, putLoud, putNormal, putQuiet, withVerbosity, quietly,
    Resource, newResource, newResourceIO, withResource, withResources, newThrottle, newThrottleIO,
    newCache, newCacheIO,
    unsafeExtraThread, unsafeAllowApply,
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
import Development.Shake.Internal.Core.Rules
import Development.Shake.Internal.Core.Pool
import Development.Shake.Internal.Core.Database
import Development.Shake.Internal.Core.Monad
import Development.Shake.Internal.Resource
import Development.Shake.Internal.Value
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

-- | Define a built-in Shake rule.
--
--   A rule for a type of artifacts (e.g. /files/) provides:
--
-- * How to identify artifacts, given by the @key@ type.
--
-- * A way to produce a 'BuiltinResult', given the key value, the previous result, and whether
--   any dependencies have changed. Usually, this will 'userRule' to get the user-defined rules,
--   but you can use 'getUserRules' for customized matching behavior or avoid user rules entirely.
--
--   As an example, below is a simplified rule for building files, where files are identified
--   by a 'FilePath' and their state is identified by their modification time.
--   (the builtin functions 'Development.Shake.need' and 'Development.Shake.%>'
--   provide a similar rule).
--
-- @
-- newtype File = File FilePath deriving (Show, Typeable, Eq, Hashable, Binary, NFData)
-- newtype FileRule = FileRule { fromFileRule :: FilePath -> Maybe (Action ())) }
-- newtype ModTime = ...
-- getFileModtime :: FilePath -> Action ModTime
-- getFileModtime file = ...
--
-- fileRule :: 'Rules' ()
-- fileRule = 'addBuiltinRule' $ (\(File x) d dep = do
--         d2 <- getFileModtime x
--         let uptodate = d == Just d2 && not dep
--         urule <- 'userRule' fromFileRule x
--         case urule of
--             Just act | not uptodate -> do
--                 act
--                 d3 <- getFileModtime x
--                 return $ BuiltinResult (encode d3) () True (d == Just d3)
--             _ -> return $ BuiltinResult (encode d2) () False (d == Just d2)
-- @
--
--   This example instance means:
--
-- * A value of type @File@ uniquely identifies a file
--
-- * A user may add rules using the @FileRule@ type; they are executed if the modification
--   time changed or was not stored in Shake's database, or if a dependency changed.
--
-- * Running the rule stores a 'ModTime' modification time but returns '()' from 'apply'
--
-- * Rules depending on this rule will re-run if the modification time changed from its stored value.
--
--   A simple build system can be created for the instance above with:
--
-- @
-- -- Produce foo files using fooCC. For every output file \"filename.foo\" there must be an
-- -- input file named \"filename\".
-- compileFoo :: 'Rules' ()
-- compileFoo = 'alternatives' $ do
--     'addUserRule' (FileRule touch)
--     'addUserRule' (FileRule compile)
--     'action' ('apply' \"filename\")
--     where
--         compile :: FilePath -> Maybe ('Action' ())
--         compile outputFile = when (takeExtension outputFile == \"foo\") . Just $ do
--             -- figure out the name of the input file
--             let inputFile = dropExtension outputFile
--             'unit' $ 'apply' (File inputFile)
--             'unit' $ 'Development.Shake.cmd' \"fooCC\" inputFile outputFile
-- @
--
--   /Note:/ Dependencies between output and input files are /not/ expressed by
--   rules, but instead by invocations of 'apply' within the rules.
--   The timestamps of the files are only compared to themselves; Shake uses its
--   own (logical) clock for tracking dependencies.
--
-- addBuiltinRule :: (ShakeValue key, ShakeValue value) => (key -> Maybe value -> Bool -> Action (BuiltinResult value)) -> Rules ()
addBuiltinRule :: (Typeable key, Binary key, Binary vsto, Typeable vdyn) => (key -> Maybe vsto -> Bool -> Action (BuiltinResult vdyn)) -> Rules ()
addBuiltinRule act = newRules mempty{rules = Map.singleton kt f}
    where
    kt = typeOf $ (undefined :: (key -> foo) -> key) act
    f = BuiltinRule { execute = \k' vo' dep -> do
        let k = fromKeyDef k' (err "addBuiltinRule: incorrect type")
        let vo = fmap (decode . result) vo'
        fmap toDyn <$> act k vo dep
    }

-- | A simplified built-in rule that runs on every Shake invocation, caches its value between runs, and uses Eq for equality.
-- simpleCheck :: (ShakeValue key, ShakeValue value) => (key -> Action value) -> Rules ()
simpleCheck act = addBuiltinRule $ \k vo _ -> do
    v <- act k
    return $ BuiltinResult (encode v) v True (maybe False ((==) v) vo)

-- | The default user rule system, processing alternatives and priorities but disallowing multiple matching rules
userRule :: (Show k, Typeable k, Typeable a) => (a -> k -> Maybe b) -> k -> Action (Maybe b)
userRule from k = do
    u <- getUserRules
    case u of
        Nothing -> return Nothing
        Just u -> case userRuleMatch (fmap (($k) . from) u) of
            [r]:_ -> return $ Just r
            rs:_  -> liftIO $ errorMultipleRulesMatch (typeOf k) (Just $ show k) (length rs)
            []    -> return Nothing

-- | Internal main function (not exported publicly)
run :: ShakeOptions -> Rules () -> IO ()
run opts@ShakeOptions{..} rs = (if shakeLineBuffering then lineBuffering else id) $ do
    opts@ShakeOptions{..} <- if shakeThreads /= 0 then return opts else do p <- getProcessorCount; return opts{shakeThreads=p}
    start <- offsetTime
    (actions, ruleinfo) <- runRules opts rs

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
                            forM_ ks $ \(i,(key,v)) -> case v of
                                Ready ro -> do
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

-- | Execute a rule, returning the associated values. If possible, the rules will be run in parallel.
--   This function requires that appropriate rules have been added with 'rule'.
--   All @key@ values passed to 'apply' become dependencies of the 'Action'.
apply :: (ShakeValue key, ShakeValue value) => [key] -> Action [value]
apply = applyForall

-- | Return the values associated with an already-executed rule, throwing an error if the
--   rule would need to be re-run.
--   This function requires that appropriate rules have been added with 'rule'.
--   All @key@ values passed to 'applied' become dependencies of the 'Action'.
applied :: (ShakeValue key, ShakeValue value) => [key] -> Action [value]
applied ks = blockApply "'applied' key" (applyForall ks)

-- We don't want the forall in the Haddock docs
-- Don't short-circuit [] as we still want error messages
applyForall :: forall key value . (ShakeValue key, ShakeValue value) => [key] -> Action [value]
applyForall ks = do
    let tk = typeOf (err "apply key" :: key)
        tv = typeOf (err "apply type" :: value)
    Global{..} <- Action getRO
    -- this duplicates the check in runKey, but we can give better error messages here
    case Map.lookup tk globalRules of
        Nothing -> liftIO $ errorNoRuleToBuildType tk (show <$> listToMaybe ks) (Just tv)
        _ -> return ()
    vs <- applyKeyValue (map newKey ks)
    let f k (resultValue -> v) = case fromDynamic v of
            Just v -> return v
            Nothing -> liftIO $ errorRuleTypeMismatch tk (Just $ show k) (dynTypeRep v) tv
    zipWithM f ks vs

-- | The monomorphic function underlying 'apply', for those who need it
applyKeyValue :: [Key] -> Action [LiveResult]
applyKeyValue [] = return []
applyKeyValue ks = do
    global@Global{..} <- Action getRO
    stack <- Action $ getsRW localStack
    block <- Action $ getsRW localBlockApply
    (dur, dep, vs) <- Action $ captureRAW $ build globalPool globalDatabase (Ops (runKey_ global)) stack block ks
    (dur, dep, vs) <- Action $ captureRAW $ build globalPool globalDatabase (BuildKey $ runKey global) stack ks
    Action $ modifyRW $ \s -> s{localDiscount=localDiscount s + dur, localDepends=dep <> localDepends s}
    return vs

runKey :: Global -> Stack -> Step -> Key -> Maybe Result -> Bool -> Capture (Either SomeException (Bool, BuiltinResult))
runKey global@Global{globalOptions=ShakeOptions{..},..} stack step k r dirtyChildren continue = do
    time <- liftIO $ offsetTime
    let s = newLocal stack shakeVerbosity
    runAction global s (do
        let top = showTopStack stack
        let tk = typeKey k
        case Map.lookup tk globalRules of
            Nothing -> liftIO $ errorNoRuleToBuildType tk (Just $ show k) Nothing
            Just BuiltinRule{..} -> do
                liftIO $ evaluate $ rnf k
                liftIO $ globalLint $ "before building " ++ top
                putWhen Chatty $ "# " ++ show k
                let r' = if shakeRead then r else Nothing
                res <- execute k r' dirtyChildren
                when (LintFSATrace == shakeLint) trackCheckUsed
                liftIO $ globalLint $ "after building " ++ top
                dur <- liftIO time
                local <- Action $ getRW
                let ans = (res, dur, local)
                liftIO $ evaluate $ rnf ans
                return ans
                ) continue

-- | Apply a single rule, equivalent to calling 'apply' with a singleton list. Where possible,
--   use 'apply' to allow parallelism.
apply1 :: (ShakeValue key, ShakeValue value) => key -> Action value
apply1 = fmap head . apply . return

---------------------------------------------------------------------
-- TRACKING

-- | Track that a key has been used by the action preceeding it.
trackUse :: ShakeValue key => key -> Action ()
-- One of the following must be true:
-- 1) you are the one building this key (e.g. key == topStack)
-- 2) you have already been used by apply, and are on the dependency list
-- 3) someone explicitly gave you permission with trackAllow
-- 4) at the end of the rule, a) you are now on the dependency list, and b) this key itself has no dependencies (is source file)
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


trackCheckUsed :: Action ()
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
trackChange :: ShakeValue key => key -> Action ()
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
trackAllow :: ShakeValue key => (key -> Bool) -> Action ()
trackAllow = trackAllowForall

-- We don't want the forall in the Haddock docs
trackAllowForall :: forall key . ShakeValue key => (key -> Bool) -> Action ()
trackAllowForall test = do
    Global{..} <- Action getRO
    when (basicLint $ shakeLint globalOptions) $ Action $ modifyRW $ \s -> s{localTrackAllows = f : localTrackAllows s}
    where
        tk = typeOf (err "trackAllow key" :: key)
        f k = typeKey k == tk && fmap test (fromKey k) == Just True

---------------------------------------------------------------------
-- RESOURCES

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
newResource :: String -> Int -> Rules Resource
newResource name mx = liftIO $ newResourceIO name mx


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
newThrottle :: String -> Int -> Double -> Rules Resource
newThrottle name count period = liftIO $ newThrottleIO name count period

-- | Run an action which uses part of a finite resource. For more details see 'Resource'.
--   Note that if you call 'withResource' while a resource is held, and the new resource is not
--   available, all resources held will be released while waiting for the new resource, and
--   re-acquired after; this may cause undesirable behavior. Also note that 'need' and 'apply'
--   will similarly release all resources while executing a dependency, and re-acquire them later.
withResource :: Resource -> Int -> Action a -> Action a
withResource r i act = do
    Global{..} <- Action getRO
    liftIO $ globalDiagnostic $ show r ++ " waiting to acquire " ++ show i
    offset <- liftIO offsetTime
    Action $ captureRAW $ \continue -> acquireResource r globalPool i $ continue $ Right ()
    res <- Action $ tryRAW $ fromAction $ blockApply ("Within withResource using " ++ show r) $ do
        offset <- liftIO offset
        liftIO $ globalDiagnostic $ show r ++ " acquired " ++ show i ++ " in " ++ showDuration offset
        Action $ modifyRW $ \s -> s{localDiscount = localDiscount s + offset}
        act
    liftIO $ releaseResource r globalPool i
    liftIO $ globalDiagnostic $ show r ++ " released " ++ show i
    Action $ either throwRAW return res

-- | Run an action which uses part of several finite resources. Acquires the resources in a stable
--   order, to prevent deadlock. If all rules requiring more than one resource acquire those
--   resources with a single call to 'withResources', resources will not deadlock.
withResources :: [(Resource, Int)] -> Action a -> Action a
withResources res act
    | (r,i):_ <- filter ((< 0) . snd) res = error $ "You cannot acquire a negative quantity of " ++ show r ++ ", requested " ++ show i
    | otherwise = f $ groupBy ((==) `on` fst) $ sortBy (compare `on` fst) res
    where
        f [] = act
        f (r:rs) = withResource (fst $ head r) (sum $ map snd r) $ f rs


-- | A version of 'newCache' that runs in IO, and can be called before calling 'Development.Shake.shake'.
--   Most people should use 'newCache' instead.
newCacheIO :: (Eq k, Hashable k) => (k -> Action v) -> IO (k -> Action v)
newCacheIO act = do
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
                    Left err -> Action $ throwRAW err
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

-- | Given an action on a key, produce a cached version that will execute the action at most once per key.
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
newCache :: (Eq k, Hashable k) => (k -> Action v) -> Rules (k -> Action v)
newCache = liftIO . newCacheIO


-- | Run an action without counting to the thread limit, typically used for actions that execute
--   on remote machines using barely any local CPU resources.
--   Unsafe as it allows the 'shakeThreads' limit to be exceeded.
--   You cannot depend on a rule (e.g. 'need') while the extra thread is executing.
--   If the rule blocks (e.g. calls 'withResource') then the extra thread may be used by some other action.
--   Only really suitable for calling 'cmd'/'command'.
unsafeExtraThread :: Action a -> Action a
unsafeExtraThread act = Action $ do
    Global{..} <- getRO
    stop <- liftIO $ increasePool globalPool
    res <- tryRAW $ fromAction $ blockApply "Within unsafeExtraThread" act
    liftIO stop
    captureRAW $ \continue -> (if isLeft res then addPoolHighPriority else addPoolMediumPriority) globalPool $ continue res


-- | Execute a list of actions in parallel. In most cases 'need' will be more appropriate to benefit from parallelism.
parallel :: [Action a] -> Action [a]
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
