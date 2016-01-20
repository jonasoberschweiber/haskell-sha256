module SHA256 where

import Data.Word
import Data.Bits
import Debug.Trace
import qualified Data.ByteString as B
import qualified Data.BitString as Bi
import qualified Data.ByteString.Char8
import Data.ByteString.Base16 (encode, decode)
import Numeric (showHex)

k = [ 0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5
    , 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5
    , 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3
    , 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174
    , 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc
    , 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da
    , 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7
    , 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967
    , 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13
    , 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85
    , 0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3
    , 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070
    , 0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5
    , 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3
    , 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208
    , 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2 ] :: [Word32]

h = [ 0x6a09e667 
    , 0xbb67ae85 
    , 0x3c6ef372 
    , 0xa54ff53a
    , 0x510e527f 
    , 0x9b05688c 
    , 0x1f83d9ab 
    , 0x5be0cd19 ] :: [Word32]

sha256 :: B.ByteString -> B.ByteString
sha256 x = B.pack $ concat $ map octets iterd
  where filled = fill 512 64 x
        iterd = iter compress h 512 filled

octets :: Word32 -> [Word8]
octets w = 
    [ fromIntegral (w `shiftR` 24)
    , fromIntegral (w `shiftR` 16)
    , fromIntegral (w `shiftR` 8)
    , fromIntegral w
    ]


fill :: Int -> Int -> B.ByteString -> B.ByteString
fill b r x = Bi.realizeBitStringStrict $ x' `Bi.append` Bi.from01List [0,0,0,0,0,0,0,1] `Bi.append` Bi.from01List (take s $ repeat (fromIntegral 0)) `Bi.append` lx'
  where 
    x' = Bi.bitString x
    lx = expand (fromIntegral $ Bi.length x') r
    lx' = Bi.bitString $ B.pack lx
    lf = (fromIntegral $ Bi.length x') + 8 + r
    s = ((lf `div` b) + 1) * b - lf

expand :: Word64 -> Int -> [Word8]
expand w l = foldr (\i ws -> ws ++ [fromIntegral (w `shiftR` (i * 8))]) [] [0..((l `div` 8) - 1)]

iter :: ([Word32] -> B.ByteString -> [Word32]) -> [Word32] -> Int -> B.ByteString -> [Word32]
iter f v b x = if realL == 0 then v else f (iter f v b rest) block
  where realL = B.length x * 8
        (rest, block) = B.splitAt (realL - b) x

compress :: [Word32] -> B.ByteString -> [Word32]
compress v x = [v !! 0 + b0, v !! 1 + b1, v !! 2 + b2, v !! 3 + b3, v !! 4 + b4, v !! 5 + b5, v !! 6 + b6, v !! 7 + b7]
  where
    words = split32 x
    filled = foldl (\ws i -> ws ++ [filler i ws]) words [16..63]
    (b0, b1, b2, b3, b4, b5, b6, b7) = foldl (\s i -> round' s i filled) (v !! 0, v !! 1, v !! 2, v !! 3, v !! 4, v !! 5, v !! 6, v !! 7) [0..63]

type RoundState = (Word32, Word32, Word32, Word32, Word32, Word32, Word32, Word32) 

round' :: RoundState -> Int -> [Word32] -> RoundState
round' (b0, b1, b2, b3, b4, b5, b6, b7) i ws = (t1 + t2, b0, b1, b2, b3 + t1, b4, b5, b6)
  where
    s0 = (b0 `rotateR` 2) `xor` (b0 `rotateR` 13) `xor` (b0 `rotateR` 22)
    m = (b0 .&. b1) `xor` (b0 .&. b2) `xor` (b1 .&. b2)
    t2 = s0 + m
    s1 = (b4 `rotateR` 6) `xor` (b4 `rotateR` 11) `xor` (b4 `rotateR` 25)
    c = (b4 .&. b5) `xor`  ((complement b4) .&. b6)
    t1 = b7 + s1 + c + (k !! i) + (ws !! i)

filler :: Int -> [Word32] -> Word32
filler i w = (w !! (i - 16)) + s0 + (w !! (i - 7)) + s1
  where 
    s0 = ((w !! (i - 15)) `rotateR` 7) `xor` ((w !! (i - 15)) `rotateR` 18) `xor` ((w !! (i - 15)) `shiftR` 3)
    s1 = ((w !! (i - 2)) `rotateR` 17) `xor` ((w !! (i - 2)) `rotateR` 19) `xor` ((w !! (i - 2)) `shiftR` 10)

fromOctets :: [Word8] -> Word32
fromOctets = foldl accum 0
  where accum a o = (a `shiftL` 8) .|. fromIntegral o

split32 :: B.ByteString -> [Word32]
split32 b = [ fromOctets [words !! (i * 4 + 0), words !! (i * 4 + 1), words !! (i * 4 + 2), words !! (i * 4 + 3)] | i <- [0..15] ]
  where words = B.unpack b

p = Data.ByteString.Char8.pack

sample = p "The quick brown fox jumps over the lazy dog"

