{-# LANGUAGE MultiParamTypeClasses, GeneralizedNewtypeDeriving, DeriveDataTypeable #-}

-- | These are the additional rule types required by Makefile
module Development.Make.Rules(
    need_, want_,
    defaultRuleFile_,
    (??>), Phony(..)
    ) where

import Control.Monad.IO.Class
import System.Directory
import Control.Applicative
import Prelude

import Development.Shake
import Development.Shake.Core
import Development.Shake.Classes
import Development.Shake.FilePath

-- Internal imports
import General.String(BSU, unpackU, packU)
import Development.Shake.FileInfo(ModTime, getFileInfo)

infix 1 ??>

---------------------------------------------------------------------
-- FILE_ RULES
-- These are like file rules, but a rule may not bother creating the result
-- Which matches the (insane) semantics of make
-- If a file is not produced, it will rebuild forever

newtype File_Q = File_Q BSU
    deriving (Typeable,Eq,Hashable,Binary,NFData)

instance Show File_Q where show (File_Q x) = unpackU x

newtype File_A = File_A (Maybe ModTime)
    deriving (Typeable,Eq,Hashable,Binary,Show,NFData)

instance Rule File_Q File_A where
    analyseR _ (File_Q x) (File_A v) = (\x -> if v == fmap fst x then Continue else Rebuild) <$> getFileInfo x

defaultRuleFile_ :: Rules ()
defaultRuleFile_ = priority 0 $ rule $ \(File_Q x) -> Just $ \vo -> liftIO $ do
    res <- getFileInfo x
    case res of
        Nothing -> error $ "Error, file does not exist and no rule available:\n  " ++ unpackU x
        Just (mt,_) -> do
          let v = File_A $ Just mt
          return $ (v, vo == Just v)


need_ :: [FilePath] -> Action ()
need_ xs = (apply $ map (File_Q . packU) xs :: Action [File_A]) >> return ()

want_ :: [FilePath] -> Rules ()
want_ = action . need_

data Phony = Phony | NotPhony deriving Eq

(??>) :: (FilePath -> Bool) -> (FilePath -> Action Phony) -> Rules ()
(??>) test act = rule $ \(File_Q x_) -> let x = unpackU x_ in
    if not $ test x then Nothing else Just $ \vo -> do
        liftIO $ createDirectoryIfMissing True $ takeDirectory x
        res <- act x
        v <- liftIO $ fmap (File_A . fmap fst) $ if res == Phony
            then return Nothing
            else getFileInfo x_
        return (v, vo == Just v)
