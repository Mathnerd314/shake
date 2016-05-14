{-# LANGUAGE MultiParamTypeClasses, GeneralizedNewtypeDeriving, DeriveDataTypeable, ScopedTypeVariables #-}

module Development.Shake.Rules.Files(
    (&?>), (&%>)
    ) where

import Control.Monad
import Control.Monad.IO.Class
import Data.Maybe
import Data.List.Extra
import System.Directory
import Control.Applicative
import Prelude

import Development.Shake.Core hiding (trackAllow)
import General.Extra
import General.String
import Development.Shake.Classes
import Development.Shake.Rules.File
import Development.Shake.FilePattern
import Development.Shake.FilePath
import Development.Shake.Types
import Development.Shake.ByteString


infix 1 &?>, &%>


newtype FilesQ = FilesQ [FileQ]
    deriving (Typeable,Eq,Hashable,Binary,NFData)



newtype FilesA = FilesA [FileA]
    deriving (Typeable,Eq,Hashable,Binary,NFData)

instance Show FilesA where show (FilesA xs) = unwords $ "Files" : map (drop 5 . show) xs

instance Show FilesQ where show (FilesQ xs) = unwords $ map (showQuote . show) xs


instance Rule FilesQ FilesA where
    storedValue opts (FilesQ xs) = (fmap FilesA . sequence) <$> mapM (storedValue opts) xs
    equalValue opts (FilesQ qs) (FilesA xs) (FilesA ys)
        | let n = length qs in n /= length xs || n /= length ys = NotEqual
        | otherwise = foldr and_ EqualCheap (zipWith3 (equalValue opts) qs xs ys)
            where and_ NotEqual x = NotEqual
                  and_ EqualCheap x = x
                  and_ EqualExpensive x = if x == NotEqual then NotEqual else EqualExpensive


-- | Define a rule for building multiple files at the same time.
--   Think of it as the AND (@&&@) equivalent of '%>'.
--   As an example, a single invocation of GHC produces both @.hi@ and @.o@ files:
--
-- @
-- [\"*.o\",\"*.hi\"] '&%>' \\[o,hi] -> do
--     let hs = o 'Development.Shake.FilePath.-<.>' \"hs\"
--     'Development.Shake.need' ... -- all files the .hs import
--     'Development.Shake.cmd' \"ghc -c\" [hs]
-- @
--
--   However, in practice, it's usually easier to define rules with '%>' and make the @.hi@ depend
--   on the @.o@. When defining rules that build multiple files, all the 'FilePattern' values must
--   have the same sequence of @\/\/@ and @*@ wildcards in the same order.
--   This function will create directories for the result files, if necessary.
(&%>) :: [FilePattern] -> ([FilePath] -> Action ()) -> Rules ()
ps &%> act
    | not $ compatible ps = error $ unlines $
        "All patterns to &%> must have the same number and position of // and * wildcards" :
        ["* " ++ p ++ (if compatible [p, head ps] then "" else " (incompatible)") | p <- ps]
    | otherwise = do
        forM_ ps $ \p ->
            p %> \file -> do
                _ :: FilesA <- apply1 $ FilesQ $ map (FileQ . packU_ . filepathNormalise . unpackU_ . packU . substitute (extract p file)) ps
                return ()
        (if all simple ps then id else priority 0.5) $
            rule $ \(FilesQ xs_) -> let xs = map (unpackU . fromFileQ) xs_ in
                if not $ length xs == length ps && and (zipWith (?==) ps xs) then Nothing else Just $ do
                    liftIO $ mapM_ (createDirectoryIfMissing True) $ nubOrd $ map takeDirectory xs
                    trackAllow xs
                    act xs
                    getFileTimes "&%>" xs_


-- | Define a rule for building multiple files at the same time, a more powerful
--   and more dangerous version of '&%>'. Think of it as the AND (@&&@) equivalent of '?>'.
--
--   Given an application @test &?> ...@, @test@ should return @Just@ if the rule applies, and should
--   return the list of files that will be produced. This list /must/ include the file passed as an argument and should
--   obey the invariant:
--
-- > forAll $ \x ys -> test x == Just ys ==> x `elem` ys && all ((== Just ys) . test) ys
--
--   As an example of a function satisfying the invariaint:
--
-- @
-- test x | 'Development.Shake.FilePath.takeExtension' x \`elem\` [\".hi\",\".o\"]
--        = Just ['Development.Shake.FilePath.dropExtension' x 'Development.Shake.FilePath.<.>' \"hi\", 'Development.Shake.FilePath.dropExtension' x 'Development.Shake.FilePath.<.>' \"o\"]
-- test _ = Nothing
-- @
--
--   Regardless of whether @Foo.hi@ or @Foo.o@ is passed, the function always returns @[Foo.hi, Foo.o]@.
(&?>) :: (FilePath -> Maybe [FilePath]) -> ([FilePath] -> Action ()) -> Rules ()
(&?>) test act = priority 0.5 $ do
    let norm = toStandard . normaliseEx
    let inputOutput suf inp out =
            ["Input" ++ suf ++ ":", "  " ++ inp] ++
            ["Output" ++ suf ++ ":"] ++ map ("  "++) out
    let normTest = fmap (map norm) . test
    let checkedTest x = case normTest x of
            Nothing -> Nothing
            Just ys | x `notElem` ys -> error $ unlines $
                "Invariant broken in &?>, did not return the input (after normalisation)." :
                inputOutput "" x ys
            Just ys | bad:_ <- filter ((/= Just ys) . normTest) ys -> error $ unlines $
                ["Invariant broken in &?>, not equal for all arguments (after normalisation)."] ++
                inputOutput "1" x ys ++
                inputOutput "2" bad (fromMaybe ["Nothing"] $ normTest bad)
            Just ys -> Just ys

    isJust . checkedTest ?> \x -> do
        -- FIXME: Could optimise this test by calling rule directly and returning FileA Eq Eq Eq
        --        But only saves noticable time on uncommon Change modes
        _ :: FilesA <- apply1 $ FilesQ $ map (FileQ . packU_ . filepathNormalise . unpackU_ . packU) $ fromJust $ test x
        return ()

    rule $ \(FilesQ xs_) -> let xs@(x:_) = map (unpackU . fromFileQ) xs_ in
        case checkedTest x of
            Just ys | ys == xs -> Just $ do
                liftIO $ mapM_ (createDirectoryIfMissing True) $ nubOrd $ map takeDirectory xs
                act xs
                getFileTimes "&?>" xs_
            Just ys -> error $ "Error, &?> is incompatible with " ++ show xs ++ " vs " ++ show ys
            Nothing -> Nothing


getFileTimes :: String -> [FileQ] -> Action FilesA
getFileTimes name xs = do
    opts <- getShakeOptions
    let opts2 = if shakeChange opts == ChangeModtimeAndDigestInput then opts{shakeChange=ChangeModtime} else opts
    ys <- liftIO $ mapM (storedValue opts2) xs
    case sequence ys of
        StoredValue ys -> return $ FilesA ys
        StoredMissing | not $ shakeCreationCheck opts -> return $ FilesA []
        StoredMissing -> do
            let missing = length $ filter (==StoredMissing) ys
            error $ "Error, " ++ name ++ " rule failed to build " ++ show missing ++
                    " file" ++ (if missing == 1 then "" else "s") ++ " (out of " ++ show (length xs) ++ ")" ++
                    concat ["\n  " ++ unpackU x ++ if y == StoredMissing then " - MISSING" else "" | (FileQ x,y) <- zip xs ys]
