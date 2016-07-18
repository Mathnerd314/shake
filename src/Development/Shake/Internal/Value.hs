{-# LANGUAGE ExistentialQuantification, RecordWildCards, GeneralizedNewtypeDeriving, ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses, ConstraintKinds, KindSignatures #-}
{-# LANGUAGE FlexibleInstances, DeriveGeneric, DeriveAnyClass #-}

{- |
This module implements the Key/Value types, to abstract over hetrogenous data types.
-}
module Development.Shake.Internal.Value(
    Value(..),  Key(..), ShakeValue
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
type Key = BS.ByteString
