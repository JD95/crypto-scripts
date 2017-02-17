module Lib
    ( someFunc
    ) where

import Data.List
import Data.Tuple
import qualified Data.Functor.Foldable as F
import Control.Monad.Writer.Lazy
import Control.Arrow
import Data.Char
import Data.Bits
import Control.Monad

someFunc :: IO ()
someFunc = putStrLn "someFunc"

-- Kid RSA

data KidRSA = KidRSA{m::Int, e::Int, d::Int,n::Int} deriving Show

kidRSA a b a1 b1 = KidRSA m e d n where
  m = a * b - 1
  e = a1 * m + a
  d = b1 * m + b
  n = (e*d)`div` m

encodeKidRSA p kid = ((e kid) * p) `mod` (n kid)

decodeKidRSA p kid = ((d kid) * p) `mod` (n kid)

-- Fermat Factoring

fermatFactor :: Double -> [(Double, Double)]
fermatFactor n = takeUntil (isSqrt.snd) . iterate (\(a,b) -> (a+1,((a+1)^2)-n)) $ (sqrt n, 0.0)

isSqrt :: Double -> Bool
isSqrt n = sqrt n == fromIntegral(floor (sqrt n))

-- Mod

modSteps :: Int -> Int -> [Int]
modSteps n = takeUntil ((<=)0) . iterate (flip (-) n)

-- Orpha Annie Encoding

data Direction = L | R

shiftList _ [] = []
shiftList _ [x] = [x]
shiftList L (x:xs) = xs ++ [x]
shiftList R xs = last xs : init xs

orphanAnnieSequence = "pbhmosqdfzlnevjyiwurokxagt"

annieEncodings = fmap (zip [1..]) . iterate (shiftList L) $ orphanAnnieSequence

annieCode :: (Int, Char) -> [(Int, Char)]
annieCode = head . flip filter annieEncodings . elem

decodeAnnie :: (Int, Char) -> [Int] -> Maybe String
decodeAnnie key = sequence . fmap (`lookup` annieCode key)

encodeAnnie :: String -> (Int, Char) -> Maybe [Int]
encodeAnnie message = sequence . (`fmap` message) . flip lookup . fmap swap . annieCode

crackAnnie :: [Int] -> Maybe [String]
crackAnnie message = sequence . fmap (`decodeAnnie` message) $ zip [1..26] (repeat 'p')

-- GCD

takeUntil :: (a -> Bool) -> [a] -> [a]
takeUntil = ((uncurry (++) . second ((:[]) . head)) .) . span

iterSegment = (takeUntil ((/=) 0 . snd) .) . iterate

euclidGCD = F.cata f . iterSegment (snd &&& uncurry mod)
  where f F.Nil = pure ()
        f (F.Cons i m) = record i >> m

type ResultLog a = Writer [a] a

record :: a -> Writer [a] a
record = pass . pure . (id &&& (:))

eGCD = F.cata f . iterSegment (uncurry (flip mod) &&& fst)
  where iter (a,b) (g,s,t) = (g, t - (b `div` a) * s, s)
        f (F.Cons (0, b) _) = record (b, 0, 1)
        f (F.Cons a m) = m >>= record . iter a

modInv m n = let (s,_,_) = fst (runWriter $ eGCD (m,n)) in s

toBinary :: Int -> [Int]
toBinary 0 = []
toBinary n = toBinary (n `div` 2) ++ [(n `mod` 2)]

modExp a k n = foldl f (record 1) (toBinary k) where
  f m 1 = m >>= \x -> record $ (x * x * a) `mod` n
  f m 0 = m >>= \x-> record $ (x * x) `mod` n

-- Cesar Cihper

alphabet = ['a'..'z']

caeserCipher d n = zip alphabet $ (iterate (shiftList d) alphabet) !! n

caeserShift :: Direction -> Int -> String -> Maybe String
caeserShift d n = sequence . fmap (`lookup` (caeserCipher d) n) . fmap toLower

crackCaeser :: String -> Maybe [(Int, String)]
crackCaeser message = sequence $  fmap (\n -> (,) n <$> caeserShift R n message) [0..25]

asciiIndex :: Char -> Maybe Int
asciiIndex = flip lookup (zip alphabet [0..])

-- Transposition

permuteShift n = zip alphabet ((permutations alphabet) !!n)

permuteEncode n = sequence . fmap (`lookup` permuteShift n) . fmap toLower


-- Towers of Hanoi

--transfer :: (Int, Int) -> [[a]] -> [[a]]
--transfer (a,b) xs = 
{-
ms 0 = [0]
ms n = (2^(n-1)):(ms (n-1))

checks n m = let k = (2^(n-1) `div` m) in map ((2^n)-m)[1..k]

hanoi :: [Int] -> [[[Int]]]
hanoi inputList = let moveCount = \c -> (mod ((+) 1 c) (2^(length inputList)))
                      startingBoard = [inputList, [], []]
                      checkLists = map (checks (length inputList)) (ms (length inputList))
                  in [[[]]]
-}

-- RSA

rsaEncrypt m (n,e) = m^e `mod` n
rsaDecrypt c (n,d) = c^d `mod` n

quadraticFormula a b c = let q = sqrt ((b^2) - (4*a*c))
                         in (((-1*b) + q)/2,((-1*b) - q)/2)

chineseRemainder (a,m) (b,n) = let ((_,s,t),_) = runWriter $ eGCD (m,n)
                               in (b*s*m + a*t*n) `mod` (m*n)

-- Hanoi with Binary

data Zipper a = Z [a] a [a] deriving (Show)

toZipper (x:xs) = Z [] x xs

zipLeft (Z (l:ls) m []) = Z [] l (ls ++ [m])
zipLeft (Z l m (r:rs)) = Z (l ++ [m]) r rs

insertToMid :: a -> Zipper [a] -> [[a]]
insertToMid m (Z l ms r) = l ++ [(m:ms)] ++ r 

canMoveRight (Z l (m:ms) ((n:r):rs)) = m < n
canMoveRight (Z l (m:ms) ([]:r)) = True
canMoveRight (Z ([]:ls) (m:ms) []) = True
canMoveRight (Z ((n:l):ls) (m:ms) []) = m < n
canMoveRight _ = False

hanoiMove :: Int -> Zipper [Int] -> [[Int]]
hanoiMove 0 (Z l m r) = l ++ [m] ++ r
hanoiMove d z@(Z l [] r) = hanoiMove d (zipLeft z)
hanoiMove d z@(Z l (m:ms) r)
  | d == m && canMoveRight z = insertToMid m $ zipLeft (Z l ms r)
  | d == m = insertToMid m . zipLeft . zipLeft $ (Z l ms r)
  | otherwise = hanoiMove d (zipLeft z)

moves ds = fmap (hanoiMove . (!!) ds . countTrailingZeros) ns
  where ns = concat . take 2 $ repeat ([1..(2^(length ds)-1)]::[Int])

hanoi :: [Int] -> ResultLog [[Int]]
hanoi ds = foldM (\b f -> record (f (toZipper b))) startingBoard  (moves ds)
  where startingBoard = ds:(take (length ds-1) $ repeat [])

-- Primality Test

bmod (x,n) = (x+((n-1)`div`2))`mod`n-((n-1)`div`2)

bseq :: (Int,Int) -> [Int]
bseq (b,n) = let s = countTrailingZeros (n-1)
                 c = shiftR (n-1) s
             in [bmod((b^(2^j*c))`mod`n,n) | j <- [0..(s+1)]]
