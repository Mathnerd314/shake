{-# LANGUAGE RecordWildCards, PatternGuards, ViewPatterns #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveDataTypeable, DeriveGeneric, GeneralizedNewtypeDeriving #-}

module Development.Shake.Internal.Core.Types(
    Step, initialStep, incStep,
    Depends(..), subtractDepends, finalizeDepends,
    Stack, emptyStack, topStack, stackIds, showTopStack, addStack, checkStack,
    ) where

import Development.Shake.Classes
import General.Binary
import Development.Shake.Internal.Value
import General.Intern as Intern

import qualified Data.HashSet as Set
import Data.Maybe
import Data.List
import Data.Monoid
import Prelude

---------------------------------------------------------------------
-- UTILITY TYPES

newtype Step = Step Word32 deriving (Eq,Ord,Show,Store,NFData,Hashable,Typeable)

initialStep :: Step
initialStep = Step 1

incStep (Step i) = Step $ i + 1

---------------------------------------------------------------------
-- CALL STACK

data Stack = Stack (Maybe Key) [Id] !(Set.HashSet Id)

stackIds :: Stack -> [Id]
stackIds (Stack _ xs _) = xs

addStack :: Id -> Key -> Stack -> Stack
addStack x key (Stack _ xs set) = Stack (Just key) (x:xs) (Set.insert x set)

showTopStack :: Stack -> String
showTopStack = maybe "<unknown>" show . topStack

topStack :: Stack -> Maybe Key
topStack (Stack key _ _) = key

checkStack :: [Id] -> Stack -> Maybe Id
checkStack new (Stack _ old set)
    | bad:_ <- filter (`Set.member` set) new = Just bad
    | otherwise = Nothing

emptyStack :: Stack
emptyStack = Stack Nothing [] Set.empty

---------------------------------------------------------------------
-- OPERATIONS

newtype Depends = Depends {fromDepends :: [[Id]]}
    deriving (Show,NFData,Monoid,Store)

subtractDepends :: Depends -> Depends -> Depends
subtractDepends (Depends pre) (Depends post) = Depends $ take (length post - length pre) post

finalizeDepends :: Depends -> Depends
finalizeDepends = Depends . reverse . fromDepends
