{-# LANGUAGE RecordWildCards, PatternGuards, ViewPatterns #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveDataTypeable, DeriveGeneric, GeneralizedNewtypeDeriving #-}

module Development.Shake.Internal.Core.Types(
    NonDet, Queue, newQueue, enqueuePriority, enqueue, dequeue,
    Step, initialStep, incStep,
    Depends(..), subtractDepends, finalizeDepends,
    Stack, emptyStack, topStack, stackIds, showTopStack, addStack, checkStack,
    BuiltinResult(..), Local(..), newLocal
    ) where

import Development.Shake.Classes
import General.Binary
import Development.Shake.Internal.Value
import Development.Shake.Internal.Profile
import General.Intern as Intern

import qualified Data.HashSet as Set
import Data.Maybe
import Data.List
import Data.Monoid
import Prelude

---------------------------------------------------------------------
-- UNFAIR/RANDOM QUEUE

-- Monad for non-deterministic (but otherwise pure) computations
type NonDet a = IO a

-- Left = deterministic list, Right = non-deterministic tree
data Queue a = Queue [a] (Either [a] (Tree a))

newQueue :: Bool -> Queue a
newQueue deterministic = Queue [] $ if deterministic then Left [] else Right emptyTree

enqueuePriority :: a -> Queue a -> Queue a
enqueuePriority x (Queue p t) = Queue (x:p) t

enqueue :: a -> Queue a -> Queue a
enqueue x (Queue p (Left xs)) = Queue p $ Left $ x:xs
enqueue x (Queue p (Right t)) = Queue p $ Right $ insertTree x t

dequeue :: Queue a -> NonDet (Maybe (a, Queue a))
dequeue (Queue (p:ps) t) = return $ Just (p, Queue ps t)
dequeue (Queue [] (Left (x:xs))) = return $ Just (x, Queue [] $ Left xs)
dequeue (Queue [] (Left [])) = return Nothing
dequeue (Queue [] (Right t)) = do
    bs <- randomIO
    return $ case removeTree bs t of
        Nothing -> Nothing
        Just (x,t) -> Just (x, Queue [] $ Right t)

-- A tree with fast removal. Nodes are stored at indicies 0..n-1
data Tree a = Tree {-# UNPACK #-} !Int (Map.HashMap Int a)

emptyTree :: Tree a
emptyTree = Tree 0 Map.empty

insertTree :: a -> Tree a -> Tree a
insertTree x (Tree n mp) = Tree (n+1) $ Map.insert n x mp

-- Remove an item, put the n-1 item to go in it's place
removeTree :: Int -> Tree a -> Maybe (a, Tree a)
removeTree rnd (Tree n mp)
        | n == 0 = Nothing
        | n == 1 = Just (mp Map.! 0, emptyTree)
        | i == n-1 = Just (mp Map.! i, Tree (n-1) $ Map.delete i mp)
        | otherwise = Just (mp Map.! i, Tree (n-1) $ Map.insert i (mp Map.! (n-1)) $ Map.delete (n-1) mp)
    where
        i = abs rnd `mod` n

---------------------------------------------------------------------
-- GLOBAL TIMESTEP

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
data Local = Local
    -- constants
    {localStack :: Stack
    -- stack scoped local variables
    ,localVerbosity :: Verbosity
    ,localResources :: [Resource] -- resources
    -- mutable local variables
    ,localDepends :: Depends -- built up in reverse
    ,localDiscount :: !Seconds
    ,localTraces :: [Trace] -- in reverse
    ,localTrackAllows :: [Key -> Bool]
    ,localTrackUsed :: [Key]
    }

newLocal :: Stack -> Verbosity -> Local
newLocal stack verb = Local stack verb Nothing mempty 0 [] [] []


