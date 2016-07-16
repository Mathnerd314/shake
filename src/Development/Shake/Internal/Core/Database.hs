{-# LANGUAGE RecordWildCards, PatternGuards, ViewPatterns #-}
{-# LANGUAGE MultiParamTypeClasses, Rank2Types, NondecreasingIndentation #-}
{-# LANGUAGE DeriveDataTypeable, DeriveGeneric, DeriveFunctor, GeneralizedNewtypeDeriving, DeriveAnyClass #-}

module Development.Shake.Internal.Core.Database(
    Trace(..),
    Database, withDatabase, assertFinishedDatabase,
    listDepends, lookupDependencies, Step, incStep, Result(..), LiveResult(..), Status(Ready,Error),
    Ops(..), build, Id, Depends, subtractDepends, finalizeDepends,
    progress,
    Stack, emptyStack, topStack, showStack, showTopStack,
    toReport, checkValid, listLive
    ) where

import GHC.Generics (Generic)
import Development.Shake.Classes
import General.Binary
import Development.Shake.Internal.Core.Pool
import Development.Shake.Internal.Value
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

import Data.Binary.Get
import Data.Binary.Put

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

type StatusDB = Ids.Ids (Key, Status)
type InternDB = IORef (Intern Key)

-- | Invariant: The database does not have any cycles where a Key depends on itself
data Database = Database
    {lock :: Lock
    ,intern :: InternDB
    ,status :: StatusDB
    ,oldstatus :: Ids.Ids (Key, Result)
    ,step :: {-# UNPACK #-} !Step
    ,journal :: Id -> Key -> Result -> IO ()
    ,diagnostic :: IO String -> IO () -- ^ logging function
    }

data Status
    = Ready LiveResult -- ^ I have a value
    | Error SomeException -- ^ I have been run and raised an error
    | Waiting (Waiting Status) (Maybe Result) -- ^ Checking/building subdependencies
                                              -- The Waiting is called only with Ready or Error
                                              -- The Maybe is used only for progress
      deriving Show

data Result = Result
    {result :: Value -- ^ the result to store for the Key
    ,built :: {-# UNPACK #-} !Step -- ^ when it was actually run
    ,changed :: {-# UNPACK #-} !Step -- ^ the step for deciding if it's valid
    ,depends :: Depends -- ^ dependencies (stored in order of appearance; don't run them early)
    ,execution :: {-# UNPACK #-} !Float -- ^ how long it took when it was last run (seconds)
    } deriving (Show,Generic,Store,NFData)

data LiveResult = LiveResult
    { resultValue :: Dynamic -- ^ dynamic return value limited to lifetime of the program
    , resultStore :: Result -- ^ persistent database value
    , traces :: [Trace] -- ^ a trace of the expensive operations (start/end in seconds since beginning of run)
    } deriving (Show)

instance NFData LiveResult where
  rnf (LiveResult x1 x2 x3) = rnf x2 `seq` rnf x3

---------------------------------------------------------------------
-- OPERATIONS

data Ops = Ops
    { runKey :: Id -> Key -> Maybe Result -> Bool -> Stack -> Step -> Capture Status
        -- ^ Given a Key and its previous result and if its dependencies changed, run it and return the status
    }

internKey :: InternDB -> Key -> IO Id
internKey intern k = do
    is <- readIORef intern
    case Intern.lookup k is of
        Just i -> return i
        Nothing -> do
            (is, i) <- return $ Intern.add k is
            writeIORef' intern is
            return i

atom x = let s = show x in if ' ' `elem` s then "(" ++ s ++ ")" else s

updateStatus :: Database -> Id -> Key -> Status -> IO ()
updateStatus Database{..} i k v done = do
    -- this can only be full if we're called from reportResult
    (oldk,oldv) <- fmap fst &&& fmap snd <$> Ids.lookup status i
    Ids.insert status i (k,v)
    diagnostic $ maybe "Missing" show oldv ++ " -> " ++ show v ++ ", " ++ maybe "<unknown>" show oldk
    -- assert oldk == k
    return oldv

reportResult :: Database -> Id -> Key -> Status {- Ready | Error -} -> IO ()
reportResult d@Database{..} i k res = do
    withLock lock $ do
        oldv <- updateStatus d i (k,res)
        case oldv of
            Just (_,Waiting w _) -> runWaiting w res
            _ -> return ()
    -- we leave the DB lock before appending to the journal
    case res of
        Ready (resultStore -> r) -> do
            diagnostic $ "result " ++ atom k ++ " = "++ atom (result r) ++
                          " " ++ (if built r == changed r then "(changed)" else "(unchanged)")
            journal i (k, r)
        _ -> diagnostic $ "result " ++ atom k ++ " = " ++ atom ans
            -- don't store errors

showStack :: Database -> [Id] -> IO [String]
showStack Database{..} xs = do
    forM (reverse xs) $ \x ->
        maybe "<unknown>" (show . fst) <$> Ids.lookup status x

-- | Return either an exception (crash), or (how much time you spent waiting, interned keys, key results)
-- 'build' first takes the state lock and (on a single thread) performs as many transitions as it can without waiting on a mutex or running any rules.
-- Then it releases the state lock and runs the rules in the thread pool and waits for all of them to finish
-- A build requiring no rules should not result in any thread contention.
build :: Pool -> Database -> Ops -> Stack -> Maybe String -> [Key] -> Capture (Either SomeException (Seconds,Depends,[LiveResult]))
build pool database@Database{..} Ops{..} stack maybeBlock ks continue =
    join $ withLock lock $ do
        is <- forM ks $ internKey intern

        whenJust (checkStack is stack) $ \bad -> do
            -- everything else gets thrown via Left and can be Staunch'd
            -- recursion in the rules is considered a worse error, so fails immediately
            stackStr <- showStack database (bad:stackIds stack)
            k <- fmap (show.fst) $ Ids.lookup status bad
            errorRuleRecursion stackStr k

        buildMany stack is
            (\v -> case v of Error e -> Just e; _ -> Nothing)
            (\v -> return $ continue $ case v of
                Left e -> Left e
                Right rs -> Right (0, Depends [is], map result rs)) $
            \go -> do
                time <- offsetTime
                go $ \x -> case x of
                    Left e -> addPoolHighPriority pool $ continue $ Left e
                    Right rs -> addPoolMediumPriority pool $ do dur <- time; continue $ Right (dur, Depends [is], map result rs)
                return $ return ()
    where
        type Returns a = forall b . (a -> IO b) -> (Capture a -> IO b) -> IO b
        buildMany :: Stack -> [Id] -> (Status -> Maybe a) -> Returns (Either a [Result])
        buildMany stack is test fast slow = do
            let toAnswer v | Just v <- test v = Abort v
                toAnswer (Ready v) = Continue v
            let toCompute (Waiting w _)
                    | Just block <- maybeBlock = errorNoApply (show k) (fmap show r) block
                    | otherwise = Later $ toAnswer <$> w
                toCompute x = Now $ toAnswer x

            res <- rendezvous =<< mapM (fmap toCompute . reduce stack) is
            case res of
                Now v -> fast v
                Later w -> slow (afterWaiting w)

        -- Rules for each of the following functions
        -- * Must NOT lock (assumes lock already in place)
        -- * Must have an equal return to what is stored in the db at that point
        -- * Must return one of the designated subset of values

        reduce :: Stack -> Id -> IO Status {- Ready | Error | Waiting -}
        reduce stack i = do
            let aifM x t f = maybeM f t x
            -- already built / waiting?
            aifM (Ids.lookup status i) (\(_, res) -> return res) $ do
            -- not cached - abort if we're blocked
            aifM (return maybeBlock) (errorNoApply (show k) (fmap show r)) $ do
            -- stored/cached result, see if it can be reused
            aifM (Ids.lookup i oldstatus) (\(k, r) -> check stack i k r (fromDepends $ depends r)) $ do
            -- new or old key, never run or result not stored
            aifM (Intern.lookup i is) (\k -> spawn True stack i k Nothing) $ do
            -- a random id that Shake knows nothing about
            stackStr <- showStack database (stackIds stack)
            errorNoReference stackStr (show i)

        -- | Given a Key and the dependencies yet to be checked, check them
        check :: Stack -> Id -> Key -> Result -> [[Id]] -> IO Status {- Ready | Waiting -}
        check stack i k r [] = spawn False stack i k $ Just r
        check stack i k r (ds:rest) = do
            let cont v = if isLeft v then spawn True stack i k $ Just r else check stack i k r rest
            buildMany (addStack i k stack) ds
                (\v -> case v of
                    Error _ -> Just ()
                    Ready (LiveResult {resultStore = Result{..}}) | changed > built r -> Just ()
                    _ -> Nothing)
                cont $
                \go -> do
                    (self, done) <- newWaiting
                    let w = Waiting self $ Just r
                    _ <- updateStatus database i k w
                    go $ \v -> do
                        res <- cont v
                        case res of
                            Waiting w _ -> afterWaiting w done
                            _ -> done res
                    return w

        -- | Given a Key, queue up execution and return waiting
        spawn :: Bool -> Stack -> Id -> Key -> Maybe Result -> IO Status {- Waiting -}
        spawn dirtyChildren stack i k r = do
            diagnostic $ "dirty " ++ show dirtyChildren ++ " for " ++ atom k ++ " " ++ atom r
            (w', _) <- newWaiting
            let w = Waiting w' r
            _ <- updateStatus database i k w
            addPoolLowPriority pool $ runKey i k r dirtyChildren (addStack i k stack) step (reportResult database i k)
            return w

---------------------------------------------------------------------
-- PROGRESS

progress :: Database -> IO Progress
progress Database{..} = do
    xs <- Ids.toList status
    return $! foldl' f mempty $ map (snd . snd) xs
    where
        g = floatToDouble

        f s (Ready (LiveResult {resultStore = Result{..}})) = if step == built
            then s{countBuilt = countBuilt s + 1, timeBuilt = timeBuilt s + g execution}
            else s{countSkipped = countSkipped s + 1, timeSkipped = timeSkipped s + g execution}
--        f s (Loaded Result{..}) = s{countUnknown = countUnknown s + 1, timeUnknown = timeUnknown s + g execution}
        f s (Waiting _ r) =
            let (d,c) = timeTodo s
                t | Just Result{..} <- r = let d2 = d + g execution in d2 `seq` (d2,c)
                  | otherwise = let c2 = c + 1 in c2 `seq` (d,c2)
            in s{countTodo = countTodo s + 1, timeTodo = t}
        f s _ = s


---------------------------------------------------------------------
-- QUERY DATABASE

assertFinishedDatabase :: Database -> IO ()
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
resultsOnly :: Map Id (Key, Status) -> Map Id (Key, LiveResult)
resultsOnly mp = Map.map (second f) keep
    where
      keep = Map.filter (isJust . getResult . snd) mp
      f v = let Just r = getResult v
                filteredDeps = Depends . map (filter (isJust . flip Map.lookup keep)) . fromDepends $ depends r
              in
                r { resultStore = resultStore r { depends = filteredDeps } }

      getResult :: Status -> Maybe LiveResult
      getResult (Ready r) = Just r
      getResult _ = Nothing

removeStep :: Map Id (Key, LiveResult) -> Map Id (Key, LiveResult)
removeStep = Map.filter (\(k,_) -> k /= stepKey)

toReport :: Database -> IO [ProfileEntry]
toReport Database{..} = do
    status <- removeStep . resultsOnly <$> Ids.toMap status
    let order = let shw i = maybe "<unknown>" (show . fst) $ Map.lookup i status
                in dependencyOrder shw $ Map.map (concat . fromDepends . depends . resultStore . snd) status
        ids = Map.fromList $ zip order [0..]

        steps = let xs = Set.toList $ Set.fromList $ concat [[changed, built] | (_,LiveResult { resultStore = Result{..}}) <- Map.elems status]
                in Map.fromList $ zip (sortBy (flip compare) xs) [0..]

        f (k, LiveResult{resultStore=Result{..},..}) = ProfileEntry
            {prfName = show k
            ,prfBuilt = fromStep built
            ,prfChanged = fromStep changed
            ,prfDepends = mapMaybe (`Map.lookup` ids) (concat $ fromDepends depends)
            ,prfExecution = execution
            ,prfTraces = traces
            }
            where fromStep i = fromJust $ Map.lookup i steps
    return [maybe (err "toReport") f $ Map.lookup i status | i <- order]


checkValid :: Database -> [(Key, Key)] -> ([(Id, (Key, Status))] -> IO [(Key, Value, String)]) -> IO ()
checkValid Database{..} missing keyCheck = do
    intern <- readIORef intern
    diagnostic $ return "Starting validity/lint checking"

    bad <- keyCheck <$> Ids.toList status
    unless (null bad) $ do
        let n = length bad
        errorStructured
            ("Lint checking error - " ++ (if n == 1 then "value has" else show n ++ " values have")  ++ " changed since being depended upon")
            (intercalate [("",Just "")] [ [("Key", Just $ show key),("Cached value", Just $ show result),("New value", Just now)]
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


listLive :: Database -> IO [Key]
listLive Database{..} = do
    diagnostic $ return "Listing live keys"
    status <- Ids.toList status
    return [k | (_, (k, Ready{})) <- status]


listDepends :: Database -> Depends -> IO [Key]
listDepends Database{..} (Depends xs) =
    withLock lock $ do
        forM xs $ \x ->
            fst . fromJust <$> Ids.lookup status x

lookupDependencies :: Database -> Key -> IO [Key]
lookupDependencies Database{..} k =
    withLock lock $ do
        intern <- readIORef intern
        let Just i = Intern.lookup k intern
        Just (_, Ready r) <- Ids.lookup status i
        forM (concat . fromDepends . depends . resultStore $ depends r) $ \x ->
            fst . fromJust <$> Ids.lookup status x


---------------------------------------------------------------------
-- STORAGE

-- To simplify journaling etc we smuggle the Step in the database, with a special StepKey
newtype StepKey = StepKey ()
    deriving (Show,Eq,Typeable,Hashable,Store,NFData)

stepKey :: Key
stepKey = newKey $ StepKey ()

toStepResult :: Step -> LiveResult
toStepResult i = LiveResult
  { resultValue = err "Step does not have a value"
  , resultStore = Result (encode i) i i mempty 0
  , traces = [] }

fromStepResult :: Result -> Step
fromStepResult = decode . result

withDatabase :: ShakeOptions -> (IO String -> IO ()) -> (Database -> IO a) -> IO a
withDatabase opts diagnostic act = do
    registerWitness (undefined :: StepKey)
    witness <- currentWitness
    withStorage opts diagnostic witness $ \mp2 journal' -> do
        let journal i (k,v) = journal' (encode i) (encode (runPut $ putKeyWith witness k,v))
            unpack (i,t) = (decode i, case decode t of (k,s) -> (runGet (getKeyWith witness) k, s))
        let oldstatus = Map.fromList . map unpack $ Map.toList mp2
            mp1 = Intern.fromList [(k, i) | (i, (k,_)) <- Map.toList oldstatus]
        intern <- newIORef mp1
        stepId <- internKey intern stepKey
        let step = case Map.lookup stepId oldstatus of
                        Just (_,r) -> incStep . fromStepResult $ r
                        _ -> initialStep
            stepResult = toStepResult step
        status <- newIORef $ Map.singleton stepId (stepKey, Ready stepResult)
        journal stepId (stepKey, resultStore stepResult)
        lock <- newLock
        act Database{..}
