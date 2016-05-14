
module Development.Shake.Derived(
    copyFile', copyFileChanged,
    readFile', readFileLines,
    writeFile', writeFileLines, writeFileChanged,
    withTempFile, withTempDir,
    getHashedShakeVersion,
    par, forP
    ) where

import Control.Applicative
import Control.Monad.Extra
import Control.Monad.IO.Class
import System.Directory
import System.IO.Extra hiding (withTempFile, withTempDir, readFile')

import Development.Shake.Core
import Development.Shake.Rules.File
import qualified Data.ByteString as BS
import Data.Hashable
import Prelude


-- | Get a checksum of a list of files, suitable for using as `shakeVersion`.
--   This will trigger a rebuild when the Shake rules defined in any of the files are changed.
--   For example:
--
-- @
-- main = do
--     ver <- 'getHashedShakeVersion' [\"Shakefile.hs\"]
--     'shakeArgs' 'shakeOptions'{'shakeVersion' = ver} ...
-- @
--
--   To automatically detect the name of the current file, turn on the @TemplateHaskell@
--   extension and write @$(LitE . StringL . loc_filename \<$\> location)@.
--
--   This feature can be turned off during development by passing
--   the flag @--no-rule-version@ or setting 'shakeVersionIgnore' to 'True'.
getHashedShakeVersion :: [FilePath] -> IO String
getHashedShakeVersion files = do
    hashes <- mapM (fmap (hashWithSalt 0) . BS.readFile) files
    return $ "hash-" ++ show (hashWithSalt 0 hashes)


-- | @copyFile' old new@ copies the existing file from @old@ to @new@.
--   The @old@ file will be tracked as a dependency.
copyFile' :: FilePath -> FilePath -> Action ()
copyFile' old new = do
    need [old]
    putLoud $ "Copying from " ++ old ++ " to " ++ new
    liftIO $ copyFile old new


-- | @copyFileChanged old new@ copies the existing file from @old@ to @new@, if the contents have changed.
--   The @old@ file will be tracked as a dependency.
copyFileChanged :: FilePath -> FilePath -> Action ()
copyFileChanged old new = do
    need [old]
    -- in newer versions of the directory package we can use copyFileWithMetadata which (we think) updates
    -- the timestamp as well and thus no need to read the source file twice.
    unlessM (liftIO $ doesFileExist new &&^ fileEq old new) $ do
        putLoud $ "Copying from " ++ old ++ " to " ++ new
        -- copyFile does a lot of clever stuff with permissions etc, so make sure we just reuse it
        liftIO $ copyFile old new


-- | Read a file, after calling 'need'. The argument file will be tracked as a dependency.
readFile' :: FilePath -> Action String
readFile' x = need [x] >> liftIO (readFile x)

-- | Write a file, lifted to the 'Action' monad.
writeFile' :: MonadIO m => FilePath -> String -> m ()
writeFile' name x = liftIO $ writeFile name x


-- | A version of 'readFile'' which also splits the result into lines.
--   The argument file will be tracked as a dependency.
readFileLines :: FilePath -> Action [String]
readFileLines = fmap lines . readFile'

-- | A version of 'writeFile'' which writes out a list of lines.
writeFileLines :: MonadIO m => FilePath -> [String] -> m ()
writeFileLines name = writeFile' name . unlines


-- | Write a file, but only if the contents would change.
writeFileChanged :: MonadIO m => FilePath -> String -> m ()
writeFileChanged name x = liftIO $ do
    b <- doesFileExist name
    if not b then writeFile name x else do
        -- Cannot use ByteString here, since it has different line handling
        -- semantics on Windows
        b <- withFile name ReadMode $ \h -> do
            src <- hGetContents h
            return $! src /= x
        when b $ writeFile name x


-- | Create a temporary file in the temporary directory. The file will be deleted
--   after the action completes (provided the file is not still open).
--   The 'FilePath' will not have any file extension, will exist, and will be zero bytes long.
--   If you require a file with a specific name, use 'withTempDir'.
withTempFile :: (FilePath -> Action a) -> Action a
withTempFile act = do
    (file, del) <- liftIO newTempFile
    act file `actionFinally` del


-- | Create a temporary directory inside the system temporary directory.
--   The directory will be deleted after the action completes.
withTempDir :: (FilePath -> Action a) -> Action a
withTempDir act = do
    (dir,del) <- liftIO newTempDir
    act dir `actionFinally` del


-- | A 'parallel' version of 'forM'.
forP :: [a] -> (a -> Action b) -> Action [b]
forP xs f = parallel $ map f xs

-- | Execute two operations in parallel, based on 'parallel'.
par :: Action a -> Action b -> Action (a,b)
par a b = do [Left a, Right b] <- parallel [Left <$> a, Right <$> b]; return (a,b)
