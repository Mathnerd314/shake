{-# LANGUAGE ExistentialQuantification, RecordWildCards, GeneralizedNewtypeDeriving, ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses, ConstraintKinds, KindSignatures #-}
{-# LANGUAGE FlexibleInstances, DeriveGeneric, DeriveAnyClass #-}

{- |
This module implements the Key/Value types, to abstract over hetrogenous data types.
-}
module Development.Shake.Internal.Value(
    Value,  Key(..), newKey, fromKey, fromKeyDef,
    Witness, currentWitness, registerWitness,
    pokeType, putKeyWith, peekType, getKeyWith,
    ShakeValue
    ) where

import Development.Shake.Classes
import Data.Typeable.Extra

import GHC.Generics
import Data.IORef
import Data.List.Extra
import Data.Maybe
import General.Binary
import qualified Data.HashSet as Set
import qualified Data.HashMap.Strict as Map
import qualified Data.ByteString.Char8 as BS
import System.IO.Unsafe

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

type Value = BS.ByteString

data Key = Key
  { typeKey :: TypeRep
  , keyString :: Value
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
