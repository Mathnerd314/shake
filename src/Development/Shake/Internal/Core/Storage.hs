{-# LANGUAGE ScopedTypeVariables, PatternGuards, RecordWildCards, FlexibleInstances, MultiParamTypeClasses #-}
{-
This module stores the meta-data so its very important its always accurate
We can't rely on getting any exceptions or termination at the end, so we'd better write out a journal
We store a series of records, and if they contain twice as many records as needed, we compress
-}

module Development.Shake.Internal.Core.Storage(
    withStorage
    ) where

import General.Binary
import Data.Store(decodeEx)
import General.Intern
import Development.Shake.Internal.Types
import Development.Shake.Internal.Value
import General.Timing
import General.FileLock
import qualified General.Ids as Ids

import Data.Tuple.Extra
import Control.Exception.Extra
import Control.Monad.Extra
import Control.Concurrent.Extra
import Data.Time
import Data.Char
import Development.Shake.Classes
import Numeric
import System.Directory
import System.Exit
import System.FilePath
import System.IO

import Data.ByteString (ByteString)
import qualified Data.ByteString.Lazy.Char8 as LBS
import qualified Data.ByteString.Lazy as LBS8

-- Increment every time the on-disk format/semantics change,
-- @x@ is for the users version number
databaseVersion :: String -> String
-- THINGS I WANT TO DO ON THE NEXT CHANGE
-- * Change filepaths to store a 1 byte prefix saying 8bit ASCII or UTF8
-- * Duration and Time should be stored as number of 1/10000th seconds Int32
databaseVersion x = "SHAKE-DATABASE-12-" ++ s ++ "\r\n"
    where s = tail $ init $ show x -- call show, then take off the leading/trailing quotes
                                   -- ensures we do not get \r or \n in the user portion

-- Split the version off a file
splitVersion :: LBS.ByteString -> (LBS.ByteString, LBS.ByteString)
splitVersion abc = (a `LBS.append` b, c)
    where (a,bc) = LBS.break (== '\r') abc
          (b,c) = LBS.splitAt 2 bc


withStorage
    :: (Eq w, Show w, Store w)
    => ShakeOptions             -- ^ Storage options
    -> (IO String -> IO ())        -- ^ Logging function
    -> w                        -- ^ Witness
    -> (Ids.Ids Value -> (Id -> Value -> IO ()) -> IO a)  -- ^ Execute
    -> IO a
withStorage ShakeOptions{..} diagnostic witness act = withLockFileDiagnostic diagnostic (shakeFiles </> ".shake.lock") $ do
    let dbfile = shakeFiles </> ".shake.database"
        bupfile = shakeFiles </> ".shake.backup"
    createDirectoryIfMissing True shakeFiles

    -- complete a partially failed compress
    b <- doesFileExist bupfile
    when b $ do
        unexpected "Backup file exists, restoring over the previous file\n"
        diagnostic $ return "Backup file move to original"
        ignore $ removeFile dbfile
        renameFile bupfile dbfile

    addTiming "Database read"
    withBinaryFile dbfile (if shakeWrite then ReadWriteMode else ReadMode) $ \h -> do
        n <- hFileSize h
        diagnostic $ return $ "Reading file of size " ++ show n
        (oldVer,src) <- fmap splitVersion $ LBS.hGet h $ fromInteger n

        verEqual <- evaluate $ ver == oldVer -- force it so we don't leak the bytestring
        if not verEqual && not shakeVersionIgnore then do
            unless (n == 0) $ do
                let limit x = let (a,b) = splitAt 200 x in a ++ (if null b then "" else "...")
                let disp = map (\x -> if isPrint x && isAscii x then x else '?') . takeWhile (`notElem` "\r\n")
                outputErr $ unlines
                    ["Error when reading Shake database - invalid version stamp detected:"
                    ,"  File:      " ++ dbfile
                    ,"  Expected:  " ++ disp (LBS.unpack ver)
                    ,"  Found:     " ++ disp (limit $ LBS.unpack oldVer)
                    ,"All rules will be rebuilt"]
            continue h =<< Ids.empty
         else
            -- make sure you are not handling exceptions from inside
            join $ handleBool (not . asyncException) (\err -> do
                msg <- showException err
                outputErr $ unlines $
                    ("Error when reading Shake database " ++ dbfile) :
                    map ("  "++) (lines msg) ++
                    ["All files will be rebuilt"]
                when (shakeStorageLog && shakeWrite) $ do
                    hSeek h AbsoluteSeek 0
                    i <- hFileSize h
                    bs <- LBS.hGet h $ fromInteger i
                    let cor = shakeFiles </> ".shake.corrupt"
                    LBS.writeFile cor bs
                    unexpected $ "Backup of corrupted file stored at " ++ cor ++ ", " ++ show i ++ " bytes\n"

                -- exitFailure -- should never happen without external corruption
                               -- add back to check during random testing
                return $ continue h =<< Ids.empty) $
                case readChunks src of
                    ([], slop) -> do
                        when (LBS.length slop > 0) $ unexpected $ "Last " ++ show slop ++ " bytes do not form a whole record\n"
                        diagnostic $ return $ "Read 0 chunks, plus " ++ show slop ++ " slop"
                        return $ continue h =<< Ids.empty
                    (w:xs, slopRaw) -> do
                        let slop = fromIntegral $ LBS.length slopRaw
                        when (slop > 0) $ unexpected $ "Last " ++ show slop ++ " bytes do not form a whole record\n"
                        diagnostic $ return $ "Read " ++ show (length xs + 1) ++ " chunks, plus " ++ show slop ++ " slop"
                        let ws = decodeEx w
                            ents = map decodeEx xs
                        mp <- Ids.empty
                        forM_ ents $ \(k,v) -> Ids.insert mp k v

                        when (shakeVerbosity == Diagnostic) $ do
                            let raw x = "[len " ++ show (LBS.length x) ++ "] " ++ concat
                                        [['0' | length c == 1] ++ c | x <- LBS8.unpack x, let c = showHex x ""]
                            let pretty (Left x) = "FAILURE: " ++ show x
                                pretty (Right x) = x
                            diagnostic $ return $ "Witnesses " ++ raw (LBS.fromStrict w)
                            forM_ (zip3 [1..] xs ents) $ \(i,x,ent) -> do
                                x2 <- try_ $ evaluate $ let s = show ent in rnf s `seq` s
                                diagnostic $ return $ "Chunk " ++ show i ++ " " ++ raw (LBS.fromStrict x) ++ " " ++ pretty x2
                            diagnostic $ return $ "Slop " ++ raw slopRaw

                        size <- Ids.sizeUpperBound mp
                        diagnostic $ return $ "Found at most " ++ show size ++ " real entries"

                        -- if mp is null, continue will reset it, so no need to clean up
                        if verEqual && (size == 0 || (ws == witness && size * 2 > length xs - 2)) then do
                            -- make sure we reset to before the slop
                            when (size /= 0 && slop /= 0 && shakeWrite) $ do
                                diagnostic $ return $ "Dropping last " ++ show slop ++ " bytes of database (incomplete)"
                                now <- hFileSize h
                                hSetFileSize h $ now - slop
                                hSeek h AbsoluteSeek $ now - slop
                                hFlush h
                                diagnostic $ return "Drop complete"
                            return $ continue h mp
                        else if not shakeWrite then return $ continue h mp
                        else do
                            addTiming "Database compression"
                            unexpected "Compressing database\n"
                            diagnostic $ return "Compressing database"
                            hClose h -- two hClose are fine
                            return $ do
                                renameFile dbfile bupfile
                                withBinaryFile dbfile ReadWriteMode $ \h -> do
                                    reset h mp
                                    removeFile bupfile
                                    diagnostic $ return "Compression complete"
                                    continue h mp
    where
        unexpected x = when shakeStorageLog $ do
            t <- getCurrentTime
            appendFile (shakeFiles </> ".shake.storage.log") $ "\n[" ++ show t ++ "]: " ++ x
        outputErr x = do
            when (shakeVerbosity >= Quiet) $ shakeOutput Quiet x
            unexpected x

        ver = LBS.pack $ databaseVersion shakeVersion

        writeChunk h s = do
            diagnostic $ return $ "Writing chunk " ++ show (LBS.length s)
            LBS.hPut h $ toChunk s

        reset h mp = do
            diagnostic $ do
                sz <- Ids.sizeUpperBound mp
                return $ "Resetting database to at most " ++ show sz ++ " elements"
            hSetFileSize h 0
            hSeek h AbsoluteSeek 0
            LBS.hPut h ver
            writeChunk h $ LBS.fromStrict $ encode witness
            Ids.toList mp >>= mapM_ (writeChunk h . LBS.fromStrict . encode)
            hFlush h
            diagnostic $ return "Flush"

        -- continuation (since if we do a compress, h changes)
        continue h mp = do
            whenM (Ids.null mp &&^ return shakeWrite) $
                reset h mp -- might as well, no data to lose, and need to ensure a good witness table
                           -- also lets us recover in the case of corruption
            flushThread shakeWrite shakeFlush h $ \out -> do
                addTiming "With database"
                act mp $ \k v -> out . toChunk . LBS.fromStrict $ encode (k, v)


withLockFileDiagnostic :: (IO String -> IO ()) -> FilePath -> IO a -> IO a
withLockFileDiagnostic diagnostic file act = do
    diagnostic $ return $ "Before withLockFile on " ++ file
    res <- withLockFile file $ do
        diagnostic $ return "Inside withLockFile"
        act
    diagnostic $ return "After withLockFile"
    return res


-- We avoid calling flush too often on SSD drives, as that can be slow
-- Make sure all exceptions happen on the caller, so we don't have to move exceptions back
-- Make sure we only write on one thread, otherwise async exceptions can cause partial writes
flushThread :: Bool -> Maybe Double -> Handle -> ((LBS.ByteString -> IO ()) -> IO a) -> IO a
flushThread False _ h act = act (\s -> (evaluate $ LBS.length s) >> return ())
flushThread True flush h act = do
    chan <- newChan -- operations to perform on the file
    kick <- newEmptyMVar -- kicked whenever something is written
    died <- newBarrier -- has the writing thread finished

    flusher <- case flush of
        Nothing -> return Nothing
        Just flush -> fmap Just $ forkIO $ forever $ do
            takeMVar kick
            threadDelay $ ceiling $ flush * 1000000
            _ <- tryTakeMVar kick
            writeChan chan $ hFlush h >> return True

    root <- myThreadId
    writer <- forkIO $ handle_ (\e -> signalBarrier died () >> throwTo root e) $
        -- only one thread ever writes, ensuring only the final write can be torn
        whileM $ join $ readChan chan

    (act $ \s -> do
            _ <- evaluate $ LBS.length s -- ensure exceptions occur on this thread
            writeChan chan $ LBS.hPut h s >> tryPutMVar kick () >> return True)
        `finally` do
            maybe (return ()) killThread flusher
            writeChan chan $ signalBarrier died () >> return False
            waitBarrier died


-- Return the amount of junk at the end, along with all the chunk
readChunks :: LBS.ByteString -> ([ByteString], LBS.ByteString)
readChunks x
    | Just (n, x) <- grab 4 x
    , Just (y, x) <- grab (fromIntegral (decodeEx n :: Word32)) x
    = first (y :) $ readChunks x
    | otherwise = ([], x)
    where
        grab i x | LBS.length a == i = Just (LBS.toStrict a, b)
                 | otherwise = Nothing
            where (a,b) = LBS.splitAt i x


toChunk :: LBS.ByteString -> LBS.ByteString
toChunk x = n `LBS.append` x
    where n = LBS.fromStrict $ encode (fromIntegral $ LBS.length x :: Word32)


-- | Is the exception asyncronous, not a "coding error" that should be ignored
asyncException :: SomeException -> Bool
asyncException e
    | Just (_ :: AsyncException) <- fromException e = True
    | Just (_ :: ExitCode) <- fromException e = True
    | otherwise = False
