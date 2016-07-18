{-# LANGUAGE RecordWildCards, PatternGuards, ViewPatterns, ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses, Rank2Types, NondecreasingIndentation, DuplicateRecordFields #-}
{-# LANGUAGE DeriveDataTypeable, DeriveGeneric, DeriveFunctor, GeneralizedNewtypeDeriving, DeriveAnyClass #-}

module Development.Shake.Internal.Core.Database(
    Trace(..),
    Database, withDatabase, assertFinishedDatabase,
    listDepends, lookupDependencies, LiveResult(..), Result(resultStore),
    BuildKey(..), build, Id, Depends, subtractDepends, finalizeDepends,
    progress, toReport, checkValid, listLive
    ) where

import GHC.Generics (Generic)
import Development.Shake.Classes
import General.Binary
import Development.Shake.Internal.Core.Pool
import Development.Shake.Internal.Errors
import Development.Shake.Internal.Core.Storage
import Development.Shake.Internal.Types
import Development.Shake.Internal.Special
import Development.Shake.Internal.Profile
import Development.Shake.Internal.Core.Monad
import Development.Shake.Internal.Core.Rendezvous
import Development.Shake.Internal.Core.Types
import General.Extra
import General.String
import General.Intern as Intern

import Numeric.Extra
import Control.Applicative
import Control.Exception
import Control.Monad.Extra
import Control.Concurrent.Extra
import qualified Data.HashSet as Set
import qualified Data.HashMap.Strict as Map
import qualified General.Ids as Ids
import Data.Typeable.Extra

import Data.IORef.Extra
import Data.Dynamic
import Data.Maybe
import Data.List
import Data.Either.Extra
import Data.Tuple.Extra
import System.Time.Extra
import Data.Monoid
import Prelude

type Map = Map.HashMap

---------------------------------------------------------------------
-- CENTRAL TYPES

type InternDB k = IORef (Intern k)

-- | Invariant: The database does not have any cycles where a Key depends (directly or indirectly) on itself
data Database k = Database
    {lock :: Lock
    ,intern :: InternDB k
    ,status :: Ids.Ids (k, Status)
    ,step :: {-# UNPACK #-} !Step
    ,journal :: Id -> k -> Result -> IO ()
    ,diagnostic :: IO String -> IO () -- ^ logging function
    }

data Status
    = Ready LiveResult -- ^ I have a value
    | Error SomeException -- ^ I have been run and raised an error
    | Waiting (Waiting Status) -- ^ Checking/building subdependencies
                               -- The Waiting is called only with Ready or Error
    | Loaded Result -- ^ Stored value
      deriving Show

data Result = Result
    {resultStore :: {-# UNPACK #-} !ByteString -- ^ the result to store for the Key
    ,built :: {-# UNPACK #-} !Step -- ^ when it was actually run
    ,changed :: {-# UNPACK #-} !Step -- ^ the step for deciding if it's valid
    ,depends :: Depends -- ^ dependencies (stored in order of appearance; don't run them early)
    ,execution :: {-# UNPACK #-} !Float -- ^ how long it took when it was last run (seconds)
    } deriving (Show,Generic,Store,NFData)

data LiveResult = LiveResult
    {resultValue :: Dynamic -- ^ dynamic return value limited to lifetime of the program
    ,built :: {-# UNPACK #-} !Step -- ^ when it was actually run
    ,changed :: {-# UNPACK #-} !Step -- ^ the step for deciding if it's valid
    ,depends :: Depends -- ^ dependencies (stored in order of appearance; don't run them early)
    ,execution :: {-# UNPACK #-} !Float -- ^ how long it took when it was last run (seconds)
    ,traces :: [Trace] -- ^ a trace of the expensive operations (start/end in seconds since beginning of run)
    } deriving (Show,Generic,NFData)

instance NFData Dynamic where
  rnf x = x `seq` ()

---------------------------------------------------------------------
-- OPERATIONS

type BuildKey k
         = Stack -- Given the current stack with the key added on
        -> Step -- And the current step
        -> k -- The key to build
        -> Maybe Result -- A previous result, or Nothing if never been built before
        -> Bool -- True if any of the children were dirty
        -> Capture (Either SomeException (Bool, Result))
            -- Either an error, or a result.

internKey :: InternDB k -> k -> IO Id
internKey intern k = do
    is <- readIORef intern
    case Intern.lookup k is of
        Just i -> return i
        Nothing -> do
            (is, i) <- return $ Intern.add k is
            writeIORef' intern is
            return i

atom x = let s = show x in if ' ' `elem` s then "(" ++ s ++ ")" else s

updateStatus :: Database k -> Id -> k -> Status -> IO ()
updateStatus Database{..} i k v done = do
    -- this can only be full if we're called from reportResult
    (oldk,oldv) <- fmap fst &&& fmap snd <$> Ids.lookup status i
    Ids.insert status i (k,v)
    diagnostic $ maybe "Missing" show oldv ++ " -> " ++ show v ++ ", " ++ maybe "<unknown>" show oldk
    -- assert oldk == k
    return oldv

buildResult :: BuiltinResult Dynamic -> Maybe Result -> (LiveResult, Result)
buildResult Local{..} r = do
    let ldeps = finalizeDepends localDepends
        depends = if ranDependsB then ldeps else maybe ldeps (depends :: Result -> Depends) r
        changed = if unchangedB then maybe step changed r else step
        built = step
        execution = doubleToFloat $ dur - localDiscount
        traces = reverse localTraces
        ans = LiveResult { resultValue = resultValueB , ..}
        ansSto = Result { resultStore = resultStoreB , ..}
    return (ans, ansSto)


reportResult :: Database k -> Id -> k -> Either SomeException (LiveResult, Result) -> IO ()
reportResult d@Database{..} i k x = do
    res <- case x of
        Left e -> Error e
        Right r -> Ready $ fst r
    withLock lock $ do
        oldv <- updateStatus d i (k,res)
        case oldv of
            Just (_,Waiting w) -> runWaiting w res
            _ -> return ()
    -- we leave the DB lock before appending to the journal
    case x of
        Right (_,r@Result{..}) -> do
            diagnostic $ "result " ++ atom k ++ " = "++ atom (show r) ++
                          " " ++ (if built == changed then "(changed)" else "(unchanged)")
            journal i (k, r)
        _ -> diagnostic $ "result " ++ atom k ++ " = " ++ atom x
            -- don't store errors

-- getCached :: StatusDB -> Id -> Status
-- getCached status i = Ids.lookup status i (\(_, res) -> return res)

showStack :: Database k -> [Id] -> IO [String]
showStack Database{..} xs = do
    forM (reverse xs) $ \x ->
        maybe "<unknown>" (show . fst) <$> Ids.lookup status x

-- | Return (interned keys, either an exception (crash) or key results)
-- 'build' first takes the state lock and (on a single thread) performs as many transitions as it can without waiting on a mutex or running any rules.
-- Then it releases the state lock and runs the rules in the thread pool and waits for all of them to finish
-- A build requiring no rules should not result in any thread contention.

-- single threaded avoids locks and thread contention
-- parallelism spawns many threads - thread pool, shakeThreads
-- could have a mutex for each key to allow other threads to wait for a result to become available - instead, Shake has a single global state lock
-- When a rule is blocked in build, waiting for dependencies to become available, we temporarily spawn another worker
-- In order to reduce contention between processes, we run tasks in a random order
-- a deterministic order could always run all compilers followed by all linkers, resulting in lots of resource contention
-- - but now shake has resources, is this still necessary?

build :: Pool -> Database k -> BuildKey k -> Stack -> [k] -> Capture (Depends,Answer (Either SomeException [LiveResult]))
build pool database@Database{..} runKey stack ks continue =
    withLock lock $ do
        is <- forM ks $ internKey database

        whenJust (checkStack is stack) $ \bad -> do
            -- everything else gets thrown via Left and can be Staunch'd
            -- recursion in the rules is considered a worse error, so fails immediately
            stackStr <- showStack database (bad:stackIds stack)
            k <- fmap (show.fst) $ Ids.lookup status bad
            errorRuleRecursion stackStr k

        let toCompute (Waiting w) = Later w
            toCompute (Error e) = Abort e
            toCompute (Ready v) = Continue v

        res <- rendezvous $ map (fmap toCompute . reduce stack) is
        return (Depends [is], res)
    where
        -- Rules for each of the following functions
        -- * Must NOT lock (assumes lock already in place)
        -- * Must have an equal return to what is stored in the db at that point
        -- * Must return one of the designated subset of values

        reduce :: Stack -> Id -> IO Status {- Ready | Error | Waiting -}
        reduce stack i = do
            let aifM x t f = maybeM f t x
            -- already built / waiting?
            aifM (Ids.lookup status i) (\(_, res) -> return res) $ do
            -- stored/cached result, see if it can be reused
            aifM (Ids.lookup oldstatus i) (\(k, r) -> check stack i k r (fromDepends $ depends (r :: Result))) $ do
            -- new key never run or old key with no result stored
            aifM (Intern.lookup i is) (\k -> spawn True stack i k Nothing) $ do
            -- a random id that Shake knows nothing about
            stackStr <- showStack database (stackIds stack)
            errorNoReference stackStr (show i)

        -- | Given a Key and the dependencies yet to be checked, check the dependencies then run the key
        check :: Stack -> Id -> k -> Result -> [[Id]] -> IO Status {- Waiting -}
        check stack i k r [] = spawn False stack i k $ Just r
        check stack i k r (ds:rest) = do
            let cont v = if isLeft v then spawn True stack i k $ Just r else check stack i k r rest
            let stack' = addStack i k stack
            let toCompute (Waiting w) = Later $ toAnswer <$> w
                toCompute (Error _) = Abort ()
                toCompute (Ready (LiveResult {..})) | changed > built r = Abort ()
                toCompute (Ready v) = Continue v

            res <- rendezvous =<< mapM (fmap toCompute . reduce stack') ds
            case res of
                Now v -> cont v
                Wait w -> do
                    self <- newWaiting
                    let w = Waiting self
                    _ <- updateStatus database i k w
                    afterWaiting w $ \v -> do
                        res <- cont v
                        case res of
                            Waiting w -> afterWaiting w (runWaiting self)
                    return w

        -- | Given a Key, queue up execution and return waiting
        spawn :: Bool -> Stack -> Id -> k -> Maybe Result -> IO Status {- Waiting -}
        spawn dirtyChildren stack i k r = do
            diagnostic $ "dirty " ++ show dirtyChildren ++ " for " ++ atom k ++ " " ++ atom r
            w <- Waiting =<< newWaiting
            _ <- updateStatus database i k w
            addPoolLowPriority pool $ runKey (addStack i k stack) step k r dirtyChildren (reportResult database i k)
            return w

---------------------------------------------------------------------
-- PROGRESS

progress :: Database k -> IO Progress
progress Database{..} = do
    xs <- Ids.toList status
    return $! foldl' f mempty $ map (snd . snd) xs
    where
        g = floatToDouble

        f s (Ready (LiveResult {..})) = if step == built
            then s{countBuilt = countBuilt s + 1, timeBuilt = timeBuilt s + g execution}
            else s{countSkipped = countSkipped s + 1, timeSkipped = timeSkipped s + g execution}
--        f s (Loaded Result{..}) = s{countUnknown = countUnknown s + 1, timeUnknown = timeUnknown s + g execution}
        f s (Waiting r) =
            let (d,c) = timeTodo s
                t | Just Result{..} <- r = let d2 = d + g execution in d2 `seq` (d2,c)
                  | otherwise = let c2 = c + 1 in c2 `seq` (d,c2)
            in s{countTodo = countTodo s + 1, timeTodo = t}
        f s _ = s


---------------------------------------------------------------------
-- QUERY DATABASE

assertFinishedDatabase :: Database k -> IO ()
assertFinishedDatabase Database{..} = do
    -- if you have anyone Waiting, and are not exiting with an error, then must have a complex recursion (see #400)
    status <- Ids.toList status
    let bad = [key | (_, (key, Waiting{})) <- status]
    when (bad /= []) $
        errorComplexRecursion (map show bad)


-- | Given a map of representing a dependency order (with a show for error messages), find an ordering for the items such
--   that no item points to an item before itself.
--   Raise an error if you end up with a cycle.
dependencyOrder :: (Eq a, Hashable a) => (a -> String) -> Map a [a] -> [a]
-- Algorithm:
--    Divide everyone up into those who have no dependencies [Id]
--    And those who depend on a particular Id, Dep :-> Maybe [(Key,[Dep])]
--    Where d :-> Just (k, ds), k depends on firstly d, then remaining on ds
--    For each with no dependencies, add to list, then take its dep hole and
--    promote them either to Nothing (if ds == []) or into a new slot.
--    k :-> Nothing means the key has already been freed
dependencyOrder shw status = f (map fst noDeps) $ Map.map Just $ Map.fromListWith (++) [(d, [(k,ds)]) | (k,d:ds) <- hasDeps]
    where
        (noDeps, hasDeps) = partition (null . snd) $ Map.toList status

        f [] mp | null bad = []
                | otherwise = error $ unlines $
                    "Internal invariant broken, database seems to be cyclic" :
                    map ("    " ++) bad ++
                    ["... plus " ++ show (length badOverflow) ++ " more ..." | not $ null badOverflow]
            where (bad,badOverflow) = splitAt 10 [shw i | (i, Just _) <- Map.toList mp]

        f (x:xs) mp = x : f (now++xs) later
            where Just free = Map.lookupDefault (Just []) x mp
                  (now,later) = foldl' g ([], Map.insert x Nothing mp) free

        g (free, mp) (k, []) = (k:free, mp)
        g (free, mp) (k, d:ds) = case Map.lookupDefault (Just []) d mp of
            Nothing -> g (free, mp) (k, ds)
            Just todo -> (free, Map.insert d (Just $ (k,ds) : todo) mp)


-- | Eliminate all waiting / error from the database, pretending they don't exist
resultsOnly :: Map i (k, Status) -> Map i (k, LiveResult)
resultsOnly mp = Map.map (second f) keep
    where
      keep = Map.filter (isJust . getResult . snd) mp
      f v = let Just r@LiveResult{..} = getResult v
              in
                (r :: LiveResult) { depends = Depends . map (filter (isJust . flip Map.lookup keep)) . fromDepends $ depends }

      getResult :: Status -> Maybe LiveResult
      getResult (Ready r) = Just r
      getResult _ = Nothing

removeStep :: Map Id (k, LiveResult) -> Map Id (k, LiveResult)
removeStep = Map.filter (\(k,_) -> k /= stepKey)

toReport :: Database k -> IO [ProfileEntry]
toReport Database{..} = do
    status <- removeStep . resultsOnly <$> Ids.toMap status
    let order = let shw i = maybe "<unknown>" (show . fst) $ Map.lookup i status
                  in dependencyOrder shw $ Map.map (concat . fromDepends . (depends :: LiveResult -> Depends) . snd) status
        ids = Map.fromList $ zip order [0..]

        steps = let xs = Set.toList $ Set.fromList $ concat [[changed, built] | (_,LiveResult {..}) <- Map.elems status]
                in Map.fromList $ zip (sortBy (flip compare) xs) [0..]

        f (k, LiveResult{..}) = ProfileEntry
            {prfName = show k
            ,prfBuilt = fromStep built
            ,prfChanged = fromStep changed
            ,prfDepends = mapMaybe (`Map.lookup` ids) (concat $ fromDepends depends)
            ,prfExecution = execution
            ,prfTraces = traces
            }
            where fromStep i = fromJust $ Map.lookup i steps
    return [maybe (err "toReport") f $ Map.lookup i status | i <- order]


checkValid :: Database k -> [(k, k)] -> ([(Id, (k, LiveResult))] -> IO [(k, ByteString, String)]) -> IO ()
checkValid Database{..} missing keyCheck = do
    intern <- readIORef intern
    diagnostic $ return "Starting validity/lint checking"

    bad <- keyCheck <$> Map.toList . resultsOnly $ Ids.toMap status

    unless (null bad) $ do
        let n = length bad
        errorStructured
            ("Lint checking error - " ++ (if n == 1 then "value has" else show n ++ " values have")  ++ " changed since being depended upon")
            (intercalate [("",Just "")] [ [("Key", Just $ show key),("Old", Just $ show result),("New", Just now)]
                                        | (key, result, now) <- bad])
            ""

    bad <- return [(parent,key) | (parent, key) <- missing, isJust $ Intern.lookup key intern]
    unless (null bad) $ do
        let n = length bad
        errorStructured
            ("Lint checking error - " ++ (if n == 1 then "value" else show n ++ " values") ++ " did not have " ++ (if n == 1 then "its" else "their") ++ " creation tracked")
            (intercalate [("",Just "")] [ [("Rule", Just $ show parent), ("Created", Just $ show key)] | (parent,key) <- bad])
            ""

    diagnostic $ return "Validity/lint check passed"


listLive :: Database k -> IO [k]
listLive Database{..} = do
    diagnostic $ return "Listing live keys"
    status <- Ids.toList status
    return [k | (_, (k, Ready{})) <- status]


listDepends :: Database k -> Depends -> IO [k]
listDepends Database{..} (Depends xs) =
    withLock lock $ do
        forM xs $ \x ->
            fst . fromJust <$> Ids.lookup status x

lookupDependencies :: Database k -> k -> IO [k]
lookupDependencies Database{..} k =
    withLock lock $ do
        intern <- readIORef intern
        let Just i = Intern.lookup k intern
        Just (_, Ready LiveResult{..}) <- Ids.lookup status i
        forM (concat . fromDepends $ depends) $ \x ->
            fst . fromJust <$> Ids.lookup status x


---------------------------------------------------------------------
-- STORAGE

withDatabase :: ShakeOptions -> (IO String -> IO ()) -> w -> (k -> ByteString) -> (ByteString -> k) -> (Database k -> IO a) -> IO a
withDatabase opts diagnostic witness writeKey readKey act = do
    withStorage opts diagnostic witness $ \mp2 journal' step -> do
        let journal i (k,v) = journal' (encode i) (encode (writeKey k,v))
            unpack (i,t) = (decode i, case decode t of (k,s) -> (readKey k, s))
        let oldstatus = Map.fromList . map unpack $ Map.toList mp2
            mp1 = Intern.fromList [(k, i) | (i, (k,_)) <- Map.toList oldstatus]
        intern <- newIORef mp1
        status <- newIORef $ Map.empty
        lock <- newLock
        act Database{..}
