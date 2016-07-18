{-# LANGUAGE RecordWildCards, PatternGuards, ViewPatterns #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveDataTypeable, DeriveGeneric, DeriveFunctor, GeneralizedNewtypeDeriving #-}

module Development.Shake.Internal.Core.Types(
    Step, initialStep, incStep,
    Depends(..), subtractDepends, finalizeDepends,
    Stack, emptyStack, topStack, stackIds, showTopStack, addStack, checkStack,
    BuiltinResult(..), Local(..), newLocal,
    ByteString
    ) where

import Development.Shake.Classes
import General.Binary
import Development.Shake.Internal.Profile
import Development.Shake.Internal.Types
import Development.Shake.Internal.Resource
import General.Intern as Intern
import System.Time.Extra
import Data.ByteString (ByteString)

import qualified Data.HashSet as Set
import Data.Maybe
import Data.Monoid
import Prelude

---------------------------------------------------------------------
-- GLOBAL TIMESTEP

newtype Step = Step Word32 deriving (Eq,Ord,Show,Store,NFData,Hashable,Typeable)

initialStep :: Step
initialStep = Step 1

incStep (Step i) = Step $ i + 1

---------------------------------------------------------------------
-- CALL STACK

data Stack = Stack (Maybe String) [Id] !(Set.HashSet Id)

stackIds :: Stack -> [Id]
stackIds (Stack _ xs _) = xs

addStack :: Id -> String -> Stack -> Stack
addStack x key (Stack _ xs set) = Stack (Just key) (x:xs) (Set.insert x set)

showTopStack :: Stack -> String
showTopStack = maybe "<unknown>" id . topStack

topStack :: Stack -> Maybe String
topStack (Stack key _ _) = key

checkStack :: [Id] -> Stack -> Maybe Id
checkStack new (Stack _ old set)
    | bad:_ <- filter (`Set.member` set) new = Just bad
    | otherwise = Nothing

emptyStack :: Stack
emptyStack = Stack Nothing [] Set.empty

---------------------------------------------------------------------
-- DEPENDENCIES

newtype Depends = Depends {fromDepends :: [[Id]]}
    deriving (Show,NFData,Monoid,Store)

subtractDepends :: Depends -> Depends -> Depends
subtractDepends (Depends pre) (Depends post) = Depends $ take (length post - length pre) post

finalizeDepends :: Depends -> Depends
finalizeDepends = Depends . reverse . fromDepends

-- | Results
data BuiltinResult value
  = NoResult -- ^ A missing result, to be filled in later by a different rule, or result in an error at the end.
  | BuiltinResult
    { resultStoreB :: Maybe (Int, Poke ()) -- ^ action to write the associated store result, or Nothing to avoid writing it
    , resultValueB :: value -- ^ dynamic return value used during the lifetime of the program
    , ranDependsB :: Bool -- ^ whether the dependencies for this rule were 'apply'-d
    , unchangedB :: Bool -- ^ whether the value is the same, so that there is no need to run reverse dependencies
    } deriving (Typeable, Functor)

-- local variables of rules
data Local k = Local
    -- constants
    {localStack :: Stack
    -- stack scoped local variables
    ,localVerbosity :: Verbosity
    ,localResources :: [Resource] -- resources
    -- mutable local variables
    ,localDepends :: Depends -- built up in reverse
    ,localDiscount :: !Seconds
    ,localTraces :: [Trace] -- in reverse
    ,localTrackAllows :: [k -> Bool]
    ,localTrackUsed :: [k]
    }

newLocal :: Stack -> Verbosity -> Local k
newLocal stack verb = Local stack verb Nothing mempty 0 [] [] []

