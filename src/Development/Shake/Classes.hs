
-- | This module reexports the six necessary type classes that every 'Rule' type must support.
--   You can use this module to define new rules without depending on the @store@, @deepseq@ and @hashable@ packages.
module Development.Shake.Classes(
    Show(..), Typeable(..), Eq(..), Hashable(..), Store(..), NFData(..)
    ) where

import Data.Hashable
import Data.Typeable
import Data.Store
import Control.DeepSeq
