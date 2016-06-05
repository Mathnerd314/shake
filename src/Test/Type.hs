
module Test.Type(sleep, module Test.Type) where

import Development.Shake hiding (copyFileChanged)
import Development.Shake.Forward
import Development.Shake.Rule() -- ensure the module gets imported, and thus tested
import General.String
import General.Extra
import Development.Shake.FileInfo
import Development.Shake.FilePath
import Paths_shake

import Control.Exception.Extra hiding (assert)
import Control.Monad.Extra
import Data.List
import Data.Maybe
import qualified Data.ByteString as BS
import System.Directory.Extra as IO
import System.Environment.Extra
import System.Random
import System.Console.GetOpt
import System.IO.Extra as IO
import System.Time.Extra
import Prelude


shaken, shakenCwd
    :: (([String] -> IO ()) -> (String -> String) -> IO ())
    -> ([String] -> (String -> String) -> Rules ())
    -> IO ()
    -> IO ()
shaken = shakenEx False
shakenCwd = shakenEx True

shakenEx
    :: Bool
    -> (([String] -> IO ()) -> (String -> String) -> IO ())
    -> ([String] -> (String -> String) -> Rules ())
    -> IO ()
    -> IO ()
shakenEx changeDir test rules sleeper = do
    -- my debug getDataFileName (in Paths) uses a cache of the Cwd
    -- make sure we force the cache before changing directory
    getDataFileName ""

    name:args <- getArgs
    when ("--sleep" `elem` args) sleeper
    putStrLn $ "## BUILD " ++ unwords (name:args)
    let forward = "--forward" `elem` args
    args <- return $ args \\ ["--sleep","--forward"]
    cwd <- getCurrentDirectory
    let out = "output/" ++ name ++ "/"
    let obj x | changeDir = if null x then "." else x
              | otherwise = if "/" `isPrefixOf` x || null x then init out ++ x else out ++ x
    let change = if changeDir then withCurrentDirectory out else id
    let unchange act = do
            new <- getCurrentDirectory
            withCurrentDirectory cwd $ do act; createDirectoryIfMissing True new -- to deal with clean
    createDirectoryIfMissing True out
    case args of
        "test":extra -> do
            putStrLn $ "## TESTING " ++ name
            -- if the extra arguments are not --quiet/--loud it's probably going to go wrong
            change $ test (\args -> withArgs (name:args ++ extra) $ unchange $ shakenEx changeDir test rules sleeper) obj
            putStrLn $ "## FINISHED TESTING " ++ name

        "clean":_ -> removeDirectoryRecursive out

        "perturb":args -> forever $ do
            del <- removeFilesRandom out
            threads <- randomRIO (1,4)
            putStrLn $ "## TESTING PERTURBATION (" ++ show del ++ " files, " ++ show threads ++ " threads)"
            shake shakeOptions{shakeFiles=out, shakeThreads=threads, shakeVerbosity=Quiet} $ rules args (out++)

        args -> do
            t <- tracker
            let (_,files,_) = getOpt Permute [] args
            opts <- return $ shakeOptions
                {shakeFiles = obj ""
                ,shakeReport = [obj "report.html"]}
            opts <- return $ if forward then forwardOptions opts else opts
                {shakeLint = t
                ,shakeLintInside = [cwd]
                ,shakeLintIgnore = map (cwd </>) [".cabal-sandbox//",".stack-work//"]}
            withArgs (args \\ files) $
                change $ shakeWithClean
                    (unchange $ removeDirectoryRecursive out)
                    opts
                    -- if you have passed sleep, supress the "no errors" warning
                    (do rules files obj; when ("--sleep" `elem` args) $ action $ return ())


tracker :: IO Lint
tracker = do
  fsatrace <- findExecutable $ "fsatrace" <.> exe
  return $ if isJust fsatrace
           then LintFSATrace
           else LintBasic

hasTracker :: IO Bool
hasTracker = do
  t <- tracker
  return $ t == LintFSATrace


shakeWithClean :: IO () -> ShakeOptions -> Rules () -> IO ()
shakeWithClean clean opts rules = shakeArgsWith opts [cleanOpt] f
    where
        cleanOpt = Option "c" ["clean"] (NoArg $ Right ()) "Clean before building."

        f extra files = do
            when (extra /= []) clean
            if "clean" `elem` files then
                clean >> return Nothing
             else
                return $ Just $ if null files then rules else want files >> withoutActions rules


unobj :: FilePath -> FilePath
unobj = dropDirectory1 . dropDirectory1

assert :: Bool -> String -> IO ()
assert b msg = unless b $ error $ "ASSERTION FAILED: " ++ msg

infix 4 ===

(===) :: (Show a, Eq a) => a -> a -> IO ()
a === b = assert (a == b) $ "failed in ===\nLHS: " ++ show a ++ "\nRHS: " ++ show b


assertExists :: FilePath -> IO ()
assertExists file = do
    b <- IO.doesFileExist file
    assert b $ "File was expected to exist, but is missing: " ++ file

assertMissing :: FilePath -> IO ()
assertMissing file = do
    b <- IO.doesFileExist file
    assert (not b) $ "File was expected to be missing, but exists: " ++ file

assertContents :: FilePath -> String -> IO ()
assertContents file want = do
    got <- IO.readFile' file
    assert (want == got) $ "File contents are wrong: " ++ file ++ "\nWANT: " ++ want ++ "\nGOT: " ++ got

assertContentsOn :: (String -> String) -> FilePath -> String -> IO ()
assertContentsOn f file want = do
    got <- IO.readFile' file
    assert (f want == f got) $ "File contents are wrong: " ++ file ++ "\nWANT: " ++ want ++ "\nGOT: " ++ got ++
                               "\nWANT (transformed): " ++ f want ++ "\nGOT (transformed): " ++ f got

assertContentsWords :: FilePath -> String -> IO ()
assertContentsWords = assertContentsOn (unwords . words)


assertContentsInfix :: FilePath -> String -> IO ()
assertContentsInfix file want = do
    got <- IO.readFile' file
    assert (want `isInfixOf` got) $ "File contents are wrong: " ++ file ++ "\nWANT (anywhere): " ++ want ++ "\nGOT: " ++ got

assertContentsUnordered :: FilePath -> [String] -> IO ()
assertContentsUnordered file xs = assertContentsOn (unlines . sort . lines) file (unlines xs)

assertException :: [String] -> IO () -> IO ()
assertException parts act = do
    res <- try_ act
    case res of
        Left err -> let s = show err in forM_ parts $ \p ->
            assert (p `isInfixOf` s) $ "Incorrect exception, missing part:\nGOT: " ++ s ++ "\nWANTED: " ++ p
        Right _ -> error $ "Expected an exception containing " ++ show parts ++ ", but succeeded"


noTest :: ([String] -> IO ()) -> (String -> String) -> IO ()
noTest build obj = do
    build ["--abbrev=output=$OUT","-j3"]
    build ["--no-build","--report=-"]
    build []


-- | Sleep long enough for the modification time resolution to catch up
sleepFileTime :: IO ()
sleepFileTime = sleep 1


sleepFileTimeCalibrate :: IO (IO ())
sleepFileTimeCalibrate = do
    let file = "output/calibrate"
    createDirectoryIfMissing True $ takeDirectory file
    -- with 10 measurements can get a bit slow, see #451
    -- if it rounds to a second then 1st will be a fraction, but 2nd will be full second
    mtimes <- forM [1..2] $ \i -> fmap fst $ duration $ do
        writeFile file $ show i
        let time = fmap (fst . fromMaybe (error "File missing during sleepFileTimeCalibrate")) $ getFileInfo $ packU file
        t1 <- time
        flip loopM 0 $ \j -> do
            writeFile file $ show (i,j)
            t2 <- time
            return $ if t1 == t2 then Left $ j+1 else Right ()
    putStrLn $ "Longest file modification time lag was " ++ show (ceiling (maximum' mtimes * 1000)) ++ "ms"
    return $ sleep $ min 1 $ maximum' mtimes * 2


removeFilesRandom :: FilePath -> IO Int
removeFilesRandom x = do
    files <- getDirectoryContentsRecursive x
    n <- randomRIO (0,length files)
    rs <- replicateM (length files) (randomIO :: IO Double)
    mapM_ (removeFile . snd) $ sort $ zip rs files
    return n


getDirectoryContentsRecursive :: FilePath -> IO [FilePath]
getDirectoryContentsRecursive dir = do
    xs <- IO.getDirectoryContents dir
    (dirs,files) <- partitionM IO.doesDirectoryExist [dir </> x | x <- xs, not $ "." `isPrefixOf` x]
    rest <- concatMapM getDirectoryContentsRecursive dirs
    return $ files++rest


copyDirectoryChanged :: FilePath -> FilePath -> IO ()
copyDirectoryChanged old new = do
    xs <- getDirectoryContentsRecursive old
    forM_ xs $ \from -> do
        let to = new </> drop (length $ addTrailingPathSeparator old) from
        createDirectoryIfMissing True $ takeDirectory to
        copyFileChanged from to


copyFileChanged :: FilePath -> FilePath -> IO ()
copyFileChanged old new = do
    good <- IO.doesFileExist new
    good <- if not good then return False else liftM2 (==) (BS.readFile old) (BS.readFile new)
    unless good $ copyFile old new
