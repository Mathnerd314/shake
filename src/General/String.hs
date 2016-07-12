{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module General.String(
    abbreviate,
    BS, pack, unpack, pack_, unpack_,
    BSU, packU, unpackU, packU_, unpackU_, requireU
    ) where

import qualified Data.ByteString as BS (any)
import qualified Data.ByteString.Char8 as BS hiding (any)
import qualified Data.ByteString.UTF8 as UTF8
import Data.List.Extra

abbreviate :: [(String,String)] -> String -> String
abbreviate [] = id
abbreviate abbrev = f
    where
        -- order so longer abbreviations are preferred
        ordAbbrev = sortOn (negate . length . fst) abbrev

        f [] = []
        f x | (to,rest):_ <- [(to,rest) | (from,to) <- ordAbbrev, Just rest <- [stripPrefix from x]] = to ++ f rest
        f (x:xs) = x : f xs

-- | ASCII ByteString
type BS = BS.ByteString
-- | Unicode ByteString
type BSU = BS.ByteString

pack :: String -> BS
pack = pack_ . BS.pack

unpack :: BS -> String
unpack = BS.unpack . unpack_

pack_ :: BS.ByteString -> BS
pack_ = id

unpack_ :: BS -> BS.ByteString
unpack_ = id

packU :: String -> BSU
packU = packU_ . UTF8.fromString

unpackU :: BSU -> String
unpackU = UTF8.toString . unpackU_

unpackU_ :: BSU -> BS.ByteString
unpackU_ = id

packU_ :: BS.ByteString -> BSU
packU_ = id

requireU :: BSU -> Bool
requireU = BS.any (>= 0x80) . unpackU_
