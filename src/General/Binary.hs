{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, DeriveFunctor, DeriveDataTypeable, Rank2Types, NoMonomorphismRestriction #-}

module General.Binary (Word16, Word32, Peek, Poke, Store(..), Size(..), contramapSize, peekBS, pokeBS, encode, decode, sizeOf) where

import Foreign.Storable (sizeOf)
import Foreign.Ptr (minusPtr)
import Data.Word
import qualified Data.ByteString as BS
import qualified Data.ByteString.Internal as BS

import Data.Store
import Data.Store.Internal
import Data.Store.Core

pokeBS :: BS.ByteString -> Poke ()
pokeBS x = let (sourceFp, sourceOffset, sourceLength) = BS.toForeignPtr x
           in pokeFromForeignPtr sourceFp sourceOffset sourceLength

peekBS :: Peek BS.ByteString
peekBS = do
  len <- Peek $ \end start -> return (start, end `minusPtr` start)
  fp <- peekToPlainForeignPtr "General.Binary.peekBS" len
  return (BS.PS fp 0 len)

{-
type ByteOffset = Int64

data Result a = Fail {-# UNPACK #-} !ByteOffset String
              -- ^ The decoder ran into the provided error at the provided offset.
              | Done a
              -- ^ The decoder has successfully finished, consuming all input
              | Leftovers {-# UNPACK #-} !ByteOffset a
              -- ^ The decoder has successfully finished, but (probably) did not consume the whole chunk,
              --   so you get the number of bytes consumed.
    deriving (Typeable,Functor)

data DecodeResult a = Result {-# UNPACK #-} !(Result a) -- ^ sufficient input has been provided to determine the result
              | Partial (Result a) (BS.ByteString -> DecodeResult a)
              -- ^ The decoder has consumed the available chunks and wants to know if there are
              -- more to continue. Use the second value if more input is available
              -- and the first otherwise.
    deriving (Typeable,Functor)

type Serializer x = Iso x (DecodeResult x) Builder BS.ByteString


bytestring :: Serializer BS.ByteString
bytestring = iso fromByteString (\bs -> fmap mconcat $ readAllPartials bs)
    where
        readAllPartials bs = Partial (Done [bs]) $ \b -> fmap (bs:) $ readAllPartials b

binary :: B.Binary x => Serializer x
binary = iso (B.execPut . B.put) (feed . translate $ B.runGetIncremental B.get)
    where
    feed :: DecodeResult x -> BS.ByteString -> DecodeResult x
    feed (Partial _ f) bs = f bs
    feed (Result (Leftovers b c)) _ = Result $ Leftovers 0 c
    feed (Result (Done c)) _ = Result $ Leftovers 0 c
    feed (Result (Fail b c)) _ = Result $ Fail 0 c

    translate :: B.Decoder x -> DecodeResult x
    translate d = case d of
        B.Done _ b c -> Result $ Leftovers b c
        B.Fail _ b c -> Result $ Fail b c
        B.Partial f -> Partial (feedNothings (f Nothing)) (\bs -> translate (f (Just bs)))

    -- keep feeding the decoder "no input" until it produces a result
    -- potentially an infinite loop, if the decoder is x = Partial (\_ -> x)
    -- (Binary has a horrible API)
    feedNothings :: B.Decoder x -> Result x
    feedNothings (B.Done _ b c) = Leftovers b c
    feedNothings (B.Fail _ b c) = Fail b c
    feedNothings (B.Partial f) = feedNothings (f Nothing)

store :: (Storable x) => Lens (Ptr x) (IO (Ptr x)) (IO x) x
store = lens peek (\s x -> poke s x >> return s)

storeByteOff :: (Storable x) => Int -> Lens (Ptr x) (IO (Ptr x)) (IO x) x
storeByteOff off = lens (\s -> peekByteOff s off) (\s x -> pokeByteOff s off x >> return s)

movePtr :: Int -> Iso' (Ptr x) (Ptr x)
movePtr i = iso (`plusPtr` i) (`plusPtr` (negate i))

lift :: (Functor f) => Iso s t a b -> (IO a -> f b) -> (s -> f (IO t))
lift f g = rmap (fmap return) (f (lmap return g))

integralIso :: (Integral a, Integral b, Num a, Num b) => Iso a a b b
integralIso = iso fromIntegral fromIntegral

m = iso (maybe (Left ()) Right) (either (const Nothing) Just) :: Iso (Maybe a) (Maybe b) (Either () a) (Either () b)

l :: Iso x (IO x) (IO (IORef x)) (IORef x)
l = iso newIORef readIORef


data P m n a c b = P (a -> m b) (b -> n c)

identity :: Applicative f => P f a a a
identity = P pure pure

mtePtr :: Applicative f => Int -> P f (Ptr a) (Ptr a) (Ptr a)
mtePtr = P (`plusPtr` i) (`plusPtr` (negate i))

indices :: forall a f. (Applicative f, Storable a) => P f [a] [Int] Int
indices = P (pure . length) (\n -> pure $ take n $ enumFromThen 0 k)
    where k = sizeOf (undefined :: a)

for2M_ as bs f = zipWithM_ f as bs
 = traverse id (zipWith f xs ys)

traverse f = sequenceA . fmap f
sequenceA = traverse id

type S a = StateT (Ptr, Int) IO a

{ size :: Either Int (x -> Int)
, write :: x -> S ()
, read :: S (Result x)
}

encode . decode = \bs -> do
    xs <- BS.unsafeUseAsCStringLen bs $ \(p, o) -> do
        n <- fromIntegral <$> (peek p :: IO Word32)
        (p,o) <- return $ (p `plusPtr` 4, o+4)
        ns :: [Word32] <- forM (take n [0..]) $ \_ -> do
            peek p
            (p,o) <- return $ (p `plusPtr` 4, o+4)
        xs <- for ns $ \i -> do
            BS.create i $ \p' -> BS.memcpy p' p i
            (p,o) <- (p+i,o+i)
    bs <- BS.create $ \(p,l) -> do
        let n = length xs
        liftIO $ poke p (fromIntegral n :: Word32)
        (p,l) <- return $ (p+4, l+4)
        for2M_ xs $ \x ->
            let i = BS.length x
            poke p (fromIntegral i :: Word32)
            (p,l) <- return $ (p `plusPtr` 4, l+4)
        forM xs $ \x -> do
            let i = BS.length x
            BS.useAsCStringLen x $ \(bs, n) -> BS.memcpy (castPtr bs) p n
            (p,l) <- (p `plusPtr` i,l+i)

{-
(byteString $ BS.unsafeCreate totalLen, unsafePerformIO $ BS.useAsCString bs) $ \p -> runReaderT p $ do
    n = fromIntegral $ length ns integralIso . storeByteOff 0 :: Word32
    ns = for2MLens (take n [4,8..]) ns storeByteOff . p :: [Word32]
    (p <- return $ p `plusPtr`, bs <- BS.drop bs) (4 + (n * 4))
    for2MMapAccumLens (scanl (+) 0 ns) (BS.splitAt (fromIntegral i)) (BS.useAsCStringLen BS.memcpy (castPtr bs) (p `plusPtr` i))


instance Encoder [BS.ByteString] where
    -- Format:
    -- n :: Word32 - number of strings
    -- ns :: [Word32]{n} - length of each string
    -- contents of each string concatenated (sum ns bytes)
    encode xs = byteString $ BS.unsafeCreate totalLen $ \p -> do
        pokeByteOff p 0 (fromIntegral n :: Word32)
        for2M_ [4,8..] ns $ \i x -> pokeByteOff p i (fromIntegral x :: Word32)
        p <- return $ p `plusPtr` (4 + (n * 4))
        for2M_ (scanl (+) 0 ns) xs $ \i x -> BS.useAsCStringLen x $ \(bs, n) ->
            BS.memcpy (castPtr bs) (p `plusPtr` i) n
        where totalLen = (4 + (n * 4) + sum ns)
              ns = map BS.length xs
              n = fromIntegral $ length ns

unsafeCreate totalLen $ \ptr -> go bss0 ptr
  where
    totalLen = checkedSum "concat" [ len | (PS _ _ len) <- bss0 ]
    go []                  !_   = return ()
    go (PS fp off len:bss) !ptr = do
      withForeignPtr fp $ \p -> memcpy ptr (p `plusPtr` off) len
      go bss (ptr `plusPtr` len)

    decode bs = unsafePerformIO $ BS.useAsCString bs $ \p -> do
        n <- fromIntegral <$> (peekByteOff p 0 :: IO Word32)
        ns :: [Word32] <- forM [1..fromIntegral n] $ \i -> peekByteOff p (i * 4)
        return $ snd $ mapAccumL (\bs i -> swap $ BS.splitAt (fromIntegral i) bs) (BS.drop (4 + (n * 4)) bs) ns

instance Encoder () where
    encode () = BS.empty
    decode _ = ()

instance Encoder Bool where
    encode False = bsFalse
    encode True = BS.empty
    decode = BS.null

-- CAF so the True ByteString is shared
bsFalse = BS.singleton 0

instance Encoder Word32 where
    encode = encodeStorable
    decode = decodeStorable


encodeStorable :: forall a . Storable a => a -> BS.ByteString
encodeStorable = \x -> BS.unsafeCreate n $ \p -> poke (castPtr p) x
    where n = sizeOf (undefined :: a)

decodeStorable :: forall a . Storable a => BS.ByteString -> a
decodeStorable = \bs -> unsafePerformIO $ BS.useAsCStringLen bs $ \(p, size) ->
        if size /= n then error "size mismatch" else peek (castPtr p)
    where n = sizeOf (undefined :: a)


encodeStorableList :: forall a . Storable a => [a] -> BS.ByteString
encodeStorableList = \xs -> BS.unsafeCreate (n * length xs) $ \p ->
    for2M_ [0,n..] xs $ \i x -> pokeByteOff (castPtr p) i x
    where n = sizeOf (undefined :: a)

decodeStorableList :: forall a . Storable a => BS.ByteString -> [a]
decodeStorableList = \bs -> unsafePerformIO $ BS.useAsCStringLen bs $ \(p, size) ->
    let (d,m) = size `divMod` n in
    if m /= 0 then error "size mismatch" else forM [0..d-1] $ \i -> peekElemOff (castPtr p) d
    where n = sizeOf (undefined :: a)

newtype BinList a = BinList {fromBinList :: [a]}

instance Show a => Show (BinList a) where show = show . fromBinList

instance Binary a => Binary (BinList a) where
    put (BinList xs) = case splitAt 254 xs of
        (_, []) -> putWord8 (genericLength xs) >> mapM_ put xs
        (a, b) -> putWord8 255 >> mapM_ put a >> put (BinList b)
    get = do
        x <- getWord8
        case x of
            255 -> do xs <- replicateM 254 get; BinList ys <- get; return $ BinList $ xs ++ ys
            n -> BinList <$> replicateM (fromInteger $ toInteger n) get


newtype BinFloat = BinFloat {fromBinFloat :: Float}

instance Show BinFloat where show = show . fromBinFloat

instance Binary BinFloat where
    put (BinFloat x) = put (convert x :: Word32)
    get = fmap (BinFloat . convert) (get :: Get Word32)


-- Originally from data-binary-ieee754 package

convert :: (Storable a, Storable b) => a -> b
convert x = U.unsafePerformIO $ alloca $ \buf -> do
    poke (castPtr buf) x
    peek buf

    -}
{-
BS.create :: Int -> (Ptr Word8 -> IO ()) -> IO BS.ByteString
create l f = mallocByteString l >>= (withForeignPtr fp $ \p -> f p >>= return $! PS fp 0 l)
BS.unsafeUseAsCStringLen :: BS.ByteString -> (Foreign.C.String.CStringLen -> IO a) -> IO a
unsafeUseAsCStringLen (PS ps s l) f = withForeignPtr ps $ \p -> f (castPtr p `plusPtr` s,l)
withForeignPtr :: ForeignPtr a -> (Ptr a -> IO b) -> IO b
mallocByteString (I# size) = IO

withForeignPtr :: ForeignPtr a -> C (Ptr a)
mallocByteString :: Int -> IO

type C = ContT a IO
type W = WriterT (Ptr Word8) C

BS.create :: Int -> W BS.ByteString
BS.unsafeUseAsCStringLen :: BS.ByteString -> W Int
create l f = mallocByteString l >>= withForeignPtr fp >>= \p -> f (p, PS fp 0 l)
unsafeUseAsCStringLen (PS ps s l) f = fmap (\p -> (castPtr p `plusPtr` s,l)) $ withForeignPtr ps

(BS.ByteString -> W Int, Int -> W Builder)
(BS.ByteString -> DecodeResult x, x -> Builder)
(IORef x -> IO x, x -> IO (IORef x))
(a -> b, b -> a)
(a -> a, a -> a)
storeByteOff :: Int -> Ptr x -> (() -> IO x, x -> IO ())
(flip take [4,8..], fromIntegral . length) :: ([a] -> Int, Int -> [b])-}
-}
