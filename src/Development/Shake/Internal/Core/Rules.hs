{-# LANGUAGE RecordWildCards, ScopedTypeVariables, PatternGuards, ViewPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor, DeriveDataTypeable, DeriveGeneric, DeriveAnyClass #-}
{-# LANGUAGE ExistentialQuantification, RankNTypes, MultiParamTypeClasses, ConstraintKinds #-}

module Development.Shake.Internal.Core.Rules(
    Action, apply, apply1,
    Rules, runRules, ShakeValue(..),
    BuiltinRule(..), addBuiltinRule, BuiltinResult(..),
    addUserRule, alternatives, priority,
    action, withoutActions
    ) where


import Control.Applicative
import Control.Exception.Extra
import Control.Monad.Extra
import Control.Monad.Fix
import Control.Monad.IO.Class
import Control.Monad.Trans.Writer.Strict
import Data.Function
import Data.IORef
import Data.List.Extra
import Data.Maybe
import Data.Monoid
import Data.Tuple.Extra
import Data.Typeable.Extra
import GHC.Generics
import General.Binary
import System.IO.Extra
import System.IO.Unsafe
import qualified Data.ByteString.Char8 as BS
import qualified Data.HashMap.Strict as Map
import qualified Data.HashSet as Set

import Development.Shake.Classes
import Development.Shake.Internal.Core.Action
import Development.Shake.Internal.Core.Database
import Development.Shake.Internal.Core.Types
import Development.Shake.Internal.Core.Run hiding (trackAllow)
import Development.Shake.Internal.Types
import Development.Shake.Internal.Errors

import Prelude


---------------------------------------------------------------------
-- RULES

--   Define a pair of types that can be used by Shake rules.
--   To import all the type classes required see "Development.Shake.Classes".
--
--   A 'Rule' instance for a class of artifacts (e.g. /files/) provides:
--
-- * How to identify individual artifacts, given by the @key@ type, e.g. with file names.
--
-- * How to describe the state of an artifact, given by the @value@ type, e.g. the file modification time.
--
-- * A way to compare two states of the same individual artifact, with 'equalValue' returning either
--   'EqualCheap' or 'NotEqual'.
--
-- * A way to query the current state of an artifact, with 'storedValue' returning the current state,
--   or 'Nothing' if there is no current state (e.g. the file does not exist).
--
--   Checking if an artifact needs to be built consists of comparing two @value@s
--   of the same @key@ with 'equalValue'. The first value is obtained by applying
--   'storedValue' to the @key@ and the second is the value stored in the build
--   database after the last successful build.
--
--   As an example, below is a simplified rule for building files, where files are identified
--   by a 'FilePath' and their state is identified by a hash of their contents
--   (the builtin functions 'Development.Shake.need' and 'Development.Shake.%>'
--   provide a similar rule).
--
-- @
-- newtype File = File FilePath deriving (Show, Typeable, Eq, Hashable, Binary, NFData)
-- newtype Modtime = Modtime Double deriving (Show, Typeable, Eq, Hashable, Binary, NFData)
-- getFileModtime file = ...
--
-- addBuiltinRule Builtininstance Rule File Modtime where
--     storedValue _ (File x) = do
--         exists <- System.Directory.doesFileExist x
--         if exists then Just \<$\> getFileModtime x else return Nothing
--     equalValue _ _ t1 t2 =
--         if t1 == t2 then EqualCheap else NotEqual
-- @
--
--   This example instance means:
--
-- * A value of type @File@ uniquely identifies a generated file.
--
-- * A value of type @Modtime@ will be used to check if a file is up-to-date.
--
--   It is important to distinguish 'Rule' instances from actual /rules/. 'Rule'
--   instances are one component required for the creation of rules.
--   Actual /rules/ are functions from a @key@ to an 'Action'; they are
--   added to 'Rules' using the 'rule' function.
--
--   A rule can be created for the instance above with:
--
-- @
-- -- Compile foo files; for every foo output file there must be a
-- -- single input file named \"filename.foo\".
-- compileFoo :: 'Rules' ()
-- compileFoo = 'rule' (Just . compile)
--     where
--         compile :: File -> 'Action' Modtime
--         compile (File outputFile) = do
--             -- figure out the name of the input file
--             let inputFile = outputFile '<.>' \"foo\"
--             'unit' $ 'Development.Shake.cmd' \"fooCC\" inputFile outputFile
--             -- return the (new) file modtime of the output file:
--             getFileModtime outputFile
-- @
--
--   /Note:/ In this example, the timestamps of the input files are never
--   used, let alone compared to the timestamps of the ouput files.
--   Dependencies between output and input files are /not/ expressed by
--   'Rule' instances. Dependencies are created automatically by 'apply'.
--
--   For rules whose values are not stored externally,
--   'storedValue' should return 'Just' with a sentinel value
--   and 'equalValue' should always return 'EqualCheap' for that sentinel.
type BuiltinRule k v = BuildKey Key
data BuiltinRule_ = forall k v. BuiltinRule_ (BuiltinRule k v)

data UserRule_ = forall a . Typeable a => UserRule_ (UserRule a)

-- | A 'Match' data type, representing user-defined rules associated with a particular type.
--   As an example '?>' and '*>' will add entries to the 'Match' data type.
--
--   /Semantics/
--
-- > priority p1 (priority p2 x) == priority p1 x
-- > priority p (x `ordered` y) = priority p x `ordered` priority p y
-- > priority p (x `unordered` y) = priority p x `unordered` priority p y
-- > ordered is associative
-- > unordered is associative and commutative
-- > alternative does not obey priorities, until picking the best one
data UserRule a
    = UserRule a
    | Unordered [UserRule a] -- ^ Added to the state with @'addUserRule' :: Typeable a => a -> Rules ()@.
    | Priority Double (UserRule a) -- ^ Rules defined under 'priority'.
    | Alternative (UserRule a) -- ^ matched in order.
      deriving (Eq,Show,Functor)

-- | Rules might be able to be optimised in some cases
userRuleMatch :: UserRule (Maybe a) -> [a]
userRuleMatch = head . map snd . reverse . groupSort . f
    where
        f :: UserRule (Maybe a) -> [(Double,a)]
        f (UserRule x) = maybe [] (\x -> [(1,x)]) x
        f (Unordered xs) = concatMap f xs
        f (Priority d x) = map (first $ const d) $ f x
        f (Alternative x) = take 1 $ f x

-- | Define a set of rules. Rules can be created with calls to functions such as 'Development.Shake.%>' or 'action'.
--   Rules are combined with either the 'Monoid' instance, or (more commonly) the 'Monad' instance and @do@ notation.
--   To define your own custom types of rule, see "Development.Shake.Rule".
newtype Rules a = Rules (WriterT SRules IO a) -- All IO must be associative/commutative (e.g. creating IORef/MVars)
    deriving (Functor, Applicative, Monad, MonadIO, MonadFix)

newRules :: SRules -> Rules ()
newRules = Rules . tell

modifyRules :: (SRules -> SRules) -> Rules () -> Rules ()
modifyRules f (Rules r) = Rules $ censor f r

getRules :: Rules () -> IO SRules
getRules (Rules r) = execWriterT r

data SRules = SRules
    {actions :: [Action ()]
    ,builtinRules :: Map.HashMap TypeRep{-k-} BuiltinRule_
    ,userRules :: Map.HashMap TypeRep{-k-} UserRule_ -- higher fst is higher priority
    }

instance Monoid SRules where
    mempty = SRules [] Map.empty Map.empty
    mappend (SRules x1 x2 x3) (SRules y1 y2 y3) = SRules (x1++y1) (Map.unionWith f x2 y2) (Map.unionWith g x3 y3)
        where
            f _ _ = err "Cannot call addBuiltinRule twice on the same key" -- TODO, proper error message
            g (UserRule_ x) (UserRule_ y) = UserRule_ $ Unordered $ fromUnordered x ++ fromUnordered (fromJust $ cast y)

            fromUnordered (Unordered xs) = xs
            fromUnordered x = [x]


instance Monoid a => Monoid (Rules a) where
    mempty = return mempty
    mappend = liftA2 mappend


-- | Add a rule to build a key, returning an appropriate 'Action' if the @key@ matches,
--   or 'Nothing' otherwise.
--   All rules at a given priority must be disjoint on all used @key@ values, with at most one match.
--   Rules have priority 1 by default, which can be modified with 'priority'.
addUserRule :: Typeable a => a -> Rules ()
addUserRule r = newRules mempty{userRules = Map.singleton (typeOf r) $ UserRule_ $ UserRule r}


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
-- newtype File = File FilePath deriving (Show, Typeable, Eq, Hashable, Store, NFData)
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
addBuiltinRule :: (ShakeValue key, ShakeValue value) => BuiltinRule key value -> Rules ()
addBuiltinRule (b :: BuildKey Key) = newRules mempty{builtinRules = Map.singleton k $ BuiltinRule_ b}
    where k = typeRep (Proxy :: Proxy key)


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



-- | Change the priority of a given set of rules, where higher priorities take precedence.
--   All matching rules at a given priority must be disjoint, or an error is raised.
--   All builtin Shake rules have priority between 0 and 1.
--   Excessive use of 'priority' is discouraged. As an example:
--
-- @
-- 'priority' 4 $ \"hello.*\" %> \\out -> 'writeFile'' out \"hello.*\"
-- 'priority' 8 $ \"*.txt\" %> \\out -> 'writeFile'' out \"*.txt\"
-- @
--
--   In this example @hello.txt@ will match the second rule, instead of raising an error about ambiguity.
--
--   The 'priority' function obeys the invariants:
--
-- @
-- 'priority' p1 ('priority' p2 r1) === 'priority' p1 r1
-- 'priority' p1 (r1 >> r2) === 'priority' p1 r1 >> 'priority' p1 r2
-- @
priority :: Double -> Rules () -> Rules ()
priority d = modifyRules $ \s -> s{userRules = Map.map f $ userRules s}
    where f (UserRule_ s) = UserRule_ $ Priority d s


-- | Change the matching behaviour of rules so rules do not have to be disjoint, but are instead matched
--   in order. Only recommended for small blocks containing a handful of rules.
--
-- @
-- 'alternatives' $ do
--     \"hello.*\" %> \\out -> 'writeFile'' out \"hello.*\"
--     \"*.txt\" %> \\out -> 'writeFile'' out \"*.txt\"
-- @
--
--   In this example @hello.txt@ will match the first rule, instead of raising an error about ambiguity.
--   Inside 'alternatives' the 'priority' of each rule is not used to determine which rule matches,
--   but the resulting match uses that priority compared to the rules outside the 'alternatives' block.
alternatives :: Rules () -> Rules ()
alternatives = modifyRules $ \r -> r{userRules = Map.map f $ userRules r}
    where f (UserRule_ s) = UserRule_ $ Alternative s


-- | Run an action, usually used for specifying top-level requirements.
--
-- @
-- main = 'Development.Shake.shake' 'shakeOptions' $ do
--    'action' $ do
--        b <- 'Development.Shake.doesFileExist' \"file.src\"
--        when b $ 'Development.Shake.need' [\"file.out\"]
-- @
--
--   This 'action' builds @file.out@, but only if @file.src@ exists. The 'action'
--   will be run in every build execution (unless 'withoutActions' is used), so only cheap
--   operations should be performed. All arguments to 'action' may be run in parallel, in any order.
--
--   For the standard requirement of only 'Development.Shake.need'ing a fixed list of files in the 'action',
--   see 'Development.Shake.want'.
action :: Action a -> Rules ()
action a = newRules mempty{actions=[void a]}


-- | Remove all actions specified in a set of rules, usually used for implementing
--   command line specification of what to build.
withoutActions :: Rules () -> Rules ()
withoutActions = modifyRules $ \x -> x{actions=[]}


runRules :: ShakeOptions -> Rules () -> IO ([Action ()], Global Key -> BuildKey Key, Witness)
runRules opts r = do
    srules <- getRules r
    return (actions srules, createRuleinfo opts srules, registerWitnesses srules)
  where
    registerWitnesses :: SRules -> IO ()
    registerWitnesses SRules{..} =
        forM_ (Map.elems builtinRules) $ registerWitness (Proxy :: Proxy k) (Proxy :: Proxy v)


    createRuleinfo :: ShakeOptions -> SRules -> Map.HashMap TypeRep (BuildKey Key)
    createRuleinfo opt SRules{..} = flip Map.map builtinRules $ (typeRep (Proxy :: Proxy v))

runKey :: Global Key -> BuildKey Key
runKey global@Global{globalOptions=ShakeOptions{..},..} stack step k r dirtyChildren continue = do
    time <- liftIO $ offsetTime
    let s = newLocal stack shakeVerbosity
    runAction global s (do
        let top = showTopStack stack
        let tk = typeKey k
        case Map.lookup tk globalRules of
            Nothing -> liftIO $ errorNoRuleToBuildType tk (Just $ show k) Nothing
            Just BuiltinRule_{} -> do
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
                let raiseError err
                        | not shakeStaunch = throwIO err
                        | otherwise = do
                            let named = abbreviate shakeAbbreviations . shakeExceptionTarget
                            atomicModifyIORef except $ \v -> (Just $ fromMaybe (named err, err) v, ())
                            -- no need to print exceptions here, they get printed when they are wrapped
                case x of
                        Left e -> Error . toException =<< shakeException global (showStack globalDatabase stack) e
                        Right r -> Ready r
                \x -> case x of
                            Left e -> raiseError =<< shakeException s0 (return ["Top-level action/want"]) e
                            Right x -> return x
                ) continue

-- To substitute a key:
-- 1. Verify substitute available & valid
-- 2. Download result into cache
-- 3. Read dependencies, substitute dependencies
-- 4. Deserialize result and update database

-- this doesn't particularly support filling a substitute dependency with a non-substitute;
-- instead, create those locally:
-- 1. build key normally
-- 2. hash results + hash of dependencies
-- 3. sign, pack, add to cache

-- to build remotely:
-- 1. check that client/server are compatible
-- 2. send key to server
-- 3. server checks & runs rule
-- 4. client waits for requests
-- 5. keys know how to send/receive/compose external state

-- fileSource = do
--   etag_nb <- readLocal
--   when server $ do
--     send clientSock (Request key etag_nb)
--     r <- recv
--     mbWrite r
--   when client $ do
--     Request key etag <- recv
--     case comp etag_nb etag of
--       Match -> send successful
--       Fixable -> send fixData
--       Error -> send error

type Action = ActionP Key

data Key = Key
  { typeKey :: TypeRep
  , keyString :: ByteString
  }
    deriving (Typeable,Eq,Show,Hashable,NFData,Generic)

pokeType :: Witness -> TypeRep -> Poke ()
pokeType ws t = do
    let msg = "no witness for " ++ show t
    poke $ fromMaybe (error msg) $ Map.lookup t (witnessOut ws)

peekType :: Witness -> Peek TypeRep
peekType ws = do
    h <- peek
    case Map.lookup h $ witnessIn ws of
        Nothing | h >= 0 && h < genericLength (typeNames ws) -> fail $
            "Failed to find a type " ++ (typeNames ws !! fromIntegral h) ++ " which is stored in the database.\n" ++
            "The most likely cause is that your build tool has changed significantly."
        Nothing -> fail $
            -- should not happen, unless proper data corruption
            "Corruption when reading Value, got type " ++ show h ++ ", but should be in range 0.." ++ show (length (typeNames ws) - 1)
        Just ty -> return ty

putKeyWith :: Witness -> Key -> Poke ()
putKeyWith ws (Key t v) = do
    pokeType ws t
    pokeBS v

getKeyWith :: Witness -> Peek Key
getKeyWith ws = do
    ty <- peekType ws
    Key ty <$> peekBS

newKey :: (Typeable a, Store a) => a -> Key
newKey a = Key (typeOf a) (encode a)

fromKey :: (Typeable a, Store a) => Key -> Maybe a
fromKey (Key t v) = case decode v of
    Right r | t == typeOf r -> Just r
            | otherwise     -> Nothing

fromKeyDef :: (Typeable a, Store a) => Key -> a -> a
fromKeyDef (Key t v) def = case decode v of
    Right r | t == typeOf r -> r
            | otherwise     -> def

---------------------------------------------------------------------
-- BINARY INSTANCES

{-# NOINLINE witness #-}
witness :: IORef (Set.HashSet TypeRep)
witness = unsafePerformIO $ newIORef Set.empty

registerWitness :: (Typeable a) => Proxy a -> IO ()
registerWitness x = registerWitness' (typeRep x)

registerWitness' :: TypeRep -> IO ()
registerWitness' x = atomicModifyIORef witness $ \mp -> (Set.insert x mp, ())

-- Produce a list in a predictable order from a Map TypeRep, which should be consistent regardless of the order
-- elements were added and stable between program executions.
-- Don't rely on the hashmap order since that might not be stable, if hashes clash.
toStableList :: Ord k => Set.HashSet k -> [k]
toStableList = sort . Set.toList

data Witness = Witness
    {typeNames :: [String] -- the canonical data, the names of the types
    ,witnessIn :: Map.HashMap Word16 TypeRep -- for reading in, find the values (some may be missing)
    ,witnessOut :: Map.HashMap TypeRep Word16 -- for writing out, find the value
    }

instance Eq Witness where
    -- Type names are produced by toStableList so should to remain consistent
    -- regardless of the order of registerWitness calls.
    a == b = typeNames a == typeNames b

currentWitness :: IO Witness
currentWitness = do
    ws <- readIORef witness
    let ks = toStableList ws
    return $ Witness (map show ks) (Map.fromList $ zip [0..] ks) (Map.fromList $ zip ks [0..])

instance Store Witness where
    size = contramapSize (\(Witness ts _ _) -> ts) size
    poke (Witness ts _ _) = poke ts
    peek = do
        ts <- peek
        let ws = toStableList $ unsafePerformIO $ readIORefAfter ts witness
        let ks = [ k | t <- ts, let k = head $ filter ((==) t . show) ws]
        return $ Witness ts (Map.fromList $ zip [0..] ks) (Map.fromList $ zip ks [0..])
        where
            -- Read an IORef after examining a variable, used to avoid GHC over-optimisation
            {-# NOINLINE readIORefAfter #-}
            readIORefAfter :: a -> IORef b -> IO b
            readIORefAfter v ref = v `seq` readIORef ref

-- | Define an alias for the six type classes required for things involved in Shake rules.
--   Using this alias requires the @ConstraintKinds@ extension.
--
--   To define your own values meeting the necessary constraints it is convenient to use the extensions
--   @GeneralizedNewtypeDeriving@ and @DeriveDataTypeable@ to write:
--
-- > newtype MyType = MyType (String, Bool) deriving (Show, Typeable, Eq, Hashable, Store, NFData)
--
--   Shake needs these instances on keys. They are used for:
--
-- * 'Show' is used to print out keys in errors, profiling, progress messages
--   and diagnostics.
--
-- * 'Typeable' is used because Shake indexes its database by the
--   type of the key involved in the rule (overlap is not
--   allowed for type classes and not allowed in Shake either);
--   this lets Shake implement built-in rules
--
-- * 'Eq' and 'Hashable' are used on keys in order to build hash maps
--   from keys to values. The 'Hashable' instances are only use at
--   runtime (never serialised to disk),
--   so they do not have to be stable across runs.
--
-- * 'Store' is used to serialize keys to and from Shake's build database
--
-- * 'NFData' is used to avoid space and thunk leaks, especially
--   when Shake is parallelized.
type ShakeValue a = (Show a, Typeable a, Eq a, Hashable a, Store a, NFData a)

-- To simplify journaling etc we smuggle the Step in the database, with a special StepKey
newtype StepKey = StepKey ()
    deriving (Show,Eq,Typeable,Hashable,Store,NFData)

stepKey :: Key
stepKey = newKey $ StepKey ()

toStepResult :: Step -> (LiveResult, Result)
toStepResult i = err "Step does not have a value"
  Result (encode i) i i mempty 0

fromStepResult :: Result -> Step
fromStepResult = decode . result

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

-- | Apply a single rule, equivalent to calling 'apply' with a singleton list. Where possible,
--   use 'apply' to allow parallelism.
apply1 :: (ShakeValue key, ShakeValue value) => key -> Action value
apply1 = fmap head . apply . return

run :: ShakeOptions -> Rules () -> IO ()
run opts@ShakeOptions{..} rs = (if shakeLineBuffering then lineBuffering else id) $ do
    opts@ShakeOptions{..} <- if shakeThreads /= 0 then return opts else do p <- getProcessorCount; return opts{shakeThreads=p}
    start <- offsetTime
    (actions, ruleinfo) <- runRules opts rs
    run' opts actions ruleinfo
--     registerWitness (undefined :: StepKey)
--     witness <- currentWitness
--         stepId <- internKey intern stepKey
--         let step = case Map.lookup stepId oldstatus of
--                         Just (_,r) -> incStep . fromStepResult $ r
--                         _ -> initialStep
--             stepResult = toStepResult step
--             stepId (stepKey, Ready stepResult)
--             journal stepId (stepKey, resultStore stepResult)

-- | Allow any matching key to violate the tracking rules.
trackAllow :: (ShakeValue key) => (key -> Bool) -> Action ()
trackAllow test = trackAllowForall
    where
        tk = typeOf (err "trackAllow key" :: key)
        f :: (key -> Bool) -> ActionP key ()
        f k = typeKey k == tk && fmap test (fromKey k) == Just True

