{-# LANGUAGE RecordWildCards, GeneralizedNewtypeDeriving, ScopedTypeVariables, PatternGuards, DeriveDataTypeable #-}
{-# LANGUAGE ExistentialQuantification, MultiParamTypeClasses, ConstraintKinds #-}

module Development.Shake.Internal.Core.Action(
    RuleInfo(..), Global(..), Local(..), Action(..),
    newLocal,
    runAction, actionOnException, actionFinally,
    getShakeOptions, getProgress, runAfter,
    getVerbosity, putWhen, putLoud, putNormal, putQuiet, withVerbosity, quietly,
    blockApply, unsafeAllowApply,
    traced
    ) where

import Control.Exception.Extra
import Control.Applicative
import Control.Monad.Extra
import Control.Monad.IO.Class
import Data.Typeable
import Data.Function
import Data.Either.Extra
import qualified Data.HashMap.Strict as Map
import Data.Maybe
import Data.IORef
import System.IO.Extra
import System.Time.Extra
import Numeric.Extra

import Development.Shake.Internal.Core.Pool
import Development.Shake.Internal.Core.Database
import Development.Shake.Internal.Core.Monad
import Development.Shake.Internal.Value
import Development.Shake.Internal.Types
import General.Cleanup
import General.String
import Prelude

---------------------------------------------------------------------
-- UNDERLYING DATA TYPE

-- | The 'Action' monad, use 'liftIO' to raise 'IO' actions into it, and 'Development.Shake.need' to execute files.
--   Action values are used by 'addUserRule' and 'action'. The 'Action' monad tracks the dependencies of a rule.
newtype Action a = Action {fromAction :: RAW Global Local a}
    deriving (Functor, Applicative, Monad, MonadIO, Typeable)

data BuiltinResult value = BuiltinResult
    { resultStoreB :: Builder -- ^ the associated store result
    , resultValueB :: value -- ^ dynamic return value limited to lifetime of the program
    , ranDependsB :: Bool -- ^ whether the dependencies for this rule were 'apply'-d
    , unchangedB :: Bool -- ^ whether the value is the same, so that there is no need to run reverse dependencies
    } deriving (Typeable, Functor)

data BuiltinRule_ = BuiltinRule_ (Key -- ^ Key that you want to build.
                               -> Maybe Result -- ^ the previous result in the database, if any
                               -> Bool -- ^ 'True' if any dependency has changed, or if Shake has no memory of this rule.
                               -> Action (BuiltinResult Dynamic) -- ^ result of executing the rule
                                 )

-- global constants of Action
data Global = Global
    {globalDatabase :: Database
    ,globalPool :: Pool
    ,globalCleanup :: Cleanup
    ,globalTimestamp :: IO Seconds
    ,globalRules :: Map.HashMap TypeRep (BuiltinRule Action)
    ,globalUserRules :: Map.HashMap TypeRep RuleSet
    ,globalOutput :: Verbosity -> String -> IO ()
    ,globalOptions  :: ShakeOptions
    ,globalDiagnostic :: String -> IO ()
    ,globalLint :: String -> IO ()
    ,globalAfter :: IORef [IO ()]
    ,globalTrackAbsent :: IORef [(Key, Key)] -- in rule fst, snd must be absent
    ,globalProgress :: IO Progress
    }

-- local variables of Action
data Local = Local
    -- constants
    {localStack :: Stack
    -- stack scoped local variables
    ,localVerbosity :: Verbosity
    ,localBlockApply ::  Maybe String -- reason to block apply, or Nothing to allow
    -- mutable local variables
    ,localDepends :: Depends -- built up in reverse
    ,localDiscount :: !Seconds
    ,localTraces :: [Trace] -- in reverse
    ,localTrackAllows :: [Key -> Bool]
    ,localTrackUsed :: [Key]
    }

newLocal :: Stack -> Verbosity -> Local
newLocal stack verb = Local stack verb Nothing [] 0 [] [] []


---------------------------------------------------------------------
-- RAW WRAPPERS

runAction :: Global -> Local -> Action a -> Capture (Either SomeException a)
runAction g l (Action x) = runRAW g l x


---------------------------------------------------------------------
-- EXCEPTION HANDLING

-- | Turn a normal exception into a ShakeException, giving it a stack and printing it out if in staunch mode.
--   If the exception is already a ShakeException (e.g. it's a child of ours who failed and we are rethrowing)
--   then do nothing with it.
shakeException :: Global -> IO [String] -> SomeException -> IO ShakeException
shakeException Global{globalOptions=ShakeOptions{..},..} stk e@(SomeException inner) = case cast inner of
    Just e@ShakeException{} -> return e
    Nothing -> do
        stk <- stk
        e <- return $ ShakeException (last $ "Unknown call stack" : stk) stk e
        when (shakeStaunch && shakeVerbosity >= Quiet) $
            globalOutput Quiet $ show e ++ "Continuing due to staunch mode"
        return e

actionBoom :: Bool -> Action a -> IO b -> Action a
actionBoom runOnSuccess act clean = do
    cleanup <- Action $ getsRO globalCleanup
    clean <- liftIO $ addCleanup cleanup $ void clean
    res <- Action $ catchRAW (fromAction act) $ \e -> liftIO (clean True) >> throwRAW e
    liftIO $ clean runOnSuccess
    return res

-- | If an exception is raised by the 'Action', perform some 'IO'.
actionOnException :: Action a -> IO b -> Action a
actionOnException = actionBoom False

-- | After an 'Action', perform some 'IO', even if there is an exception.
actionFinally :: Action a -> IO b -> Action a
actionFinally = actionBoom True


---------------------------------------------------------------------
-- QUERIES

-- | Get the initial 'ShakeOptions', these will not change during the build process.
getShakeOptions :: Action ShakeOptions
getShakeOptions = Action $ getsRO globalOptions

-- | Get the current 'Progress' structure, as would be returned by 'shakeProgress'.
getProgress :: Action Progress
getProgress = do
    res <- Action $ getsRO globalProgress
    liftIO res

-- | Specify an action to be run after the database has been closed, if building completes successfully.
runAfter :: IO () -> Action ()
runAfter op = do
    Global{..} <- Action getRO
    liftIO $ atomicModifyIORef globalAfter $ \ops -> (op:ops, ())


---------------------------------------------------------------------
-- VERBOSITY

putWhen :: Verbosity -> String -> Action ()
putWhen v msg = do
    Global{..} <- Action getRO
    verb <- getVerbosity
    when (verb >= v) $
        liftIO $ globalOutput v msg

-- | Write an unimportant message to the output, only shown when 'shakeVerbosity' is higher than normal ('Loud' or above).
--   The output will not be interleaved with any other Shake messages (other than those generated by system commands).
putLoud :: String -> Action ()
putLoud = putWhen Loud

-- | Write a normal priority message to the output, only supressed when 'shakeVerbosity' is 'Quiet' or 'Silent'.
--   The output will not be interleaved with any other Shake messages (other than those generated by system commands).
putNormal :: String -> Action ()
putNormal = putWhen Normal

-- | Write an important message to the output, only supressed when 'shakeVerbosity' is 'Silent'.
--   The output will not be interleaved with any other Shake messages (other than those generated by system commands).
putQuiet :: String -> Action ()
putQuiet = putWhen Quiet


-- | Get the current verbosity level, originally set by 'shakeVerbosity'. If you
--   want to output information to the console, you are recommended to use
--   'putLoud' \/ 'putNormal' \/ 'putQuiet', which ensures multiple messages are
--   not interleaved. The verbosity can be modified locally by 'withVerbosity'.
getVerbosity :: Action Verbosity
getVerbosity = Action $ getsRW localVerbosity

-- | Run an action with a particular verbosity level.
--   Will not update the 'shakeVerbosity' returned by 'getShakeOptions' and will
--   not have any impact on 'Diagnostic' tracing.
withVerbosity :: Verbosity -> Action a -> Action a
withVerbosity new = Action . unmodifyRW f . fromAction
    where f s0 = (s0{localVerbosity=new}, \s -> s{localVerbosity=localVerbosity s0})

-- | Run an action with 'Quiet' verbosity, in particular messages produced by 'traced'
--   (including from 'Development.Shake.cmd' or 'Development.Shake.command') will not be printed to the screen.
--   Will not update the 'shakeVerbosity' returned by 'getShakeOptions' and will
--   not turn off any 'Diagnostic' tracing.
quietly :: Action a -> Action a
quietly = withVerbosity Quiet

---------------------------------------------------------------------
-- Messing with apply

unsafeAllowApply :: Action a -> Action a
unsafeAllowApply  = applyBlockedBy Nothing

blockApply :: String -> Action a -> Action a
blockApply = applyBlockedBy . Just

applyBlockedBy :: Maybe String -> Action a -> Action a
applyBlockedBy reason = Action . unmodifyRW f . fromAction
    where f s0 = (s0{localBlockApply=reason}, \s -> s{localBlockApply=localBlockApply s0})

-- | Run an action but do not depend on anything the action uses.
--   A more general version of 'orderOnly'.
orderOnlyAction :: Action a -> Action a
orderOnlyAction act = Action $ do
    pre <- getsRW localDepends
    res <- fromAction act
    modifyRW $ \s -> s{localDepends=pre}
    return res

---------------------------------------------------------------------
-- TRACING

-- | Write an action to the trace list, along with the start/end time of running the IO action.
--   The 'Development.Shake.cmd' and 'Development.Shake.command' functions automatically call 'traced'.
--   The trace list is used for profile reports (see 'shakeReport').
--
--   By default 'traced' prints some useful extra context about what
--   Shake is building, e.g.:
--
-- > # traced message (for myobject.o)
--
--   To suppress the output of 'traced' (for example you want more control
--   over the message using 'putNormal'), use the 'quietly' combinator.
traced :: String -> IO a -> Action a
traced s a = traced' s (liftIO a)

traced' :: String -> Action a -> Action a
traced' msg act = do
    Global{..} <- Action getRO
    stack <- Action $ getsRW localStack
    start <- liftIO globalTimestamp
    putNormal $ "# " ++ msg ++ " (for " ++ showTopStack stack ++ ")"
    res <- act
    stop <- liftIO globalTimestamp
    Action $ modifyRW $ \s -> s{localTraces = Trace (pack msg) (doubleToFloat start) (doubleToFloat stop) : localTraces s}
    return res
