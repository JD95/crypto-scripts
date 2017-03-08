{-# LANGUAGE ExistentialQuantification#-}
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
import Control.Applicative



someFunc :: IO ()
someFunc = putStrLn "someFunc"

-- Kid RSA

data KidRSA = KidRSA { m::Int
                     , e::Int
                     , d::Int
                     , n::Int
                     } deriving Show


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

type ResultLog a = WriterT [a] Maybe a

record :: a -> Writer [a] a
record = pass . pure . (id &&& (:))

eGCD = F.cata f . iterSegment (uncurry (flip mod) &&& fst)
  where iter (a,b) (g,s,t) = (g, t - (b `div` a) * s, s)
        f (F.Cons (0, b) _) = record (b, 0, 1)
        f (F.Cons a m) = m >>= record . iter a

modInv m n = if n < m 
             then modInv n m
             else let (_,_,t) = fst (runWriter $ eGCD (m,n)) in t

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

-- RSA

rsaEncrypt m (n,e) = m^e `mod` n
rsaDecrypt c (n,d) = c^d `mod` n

quadraticFormula a b c = let q = sqrt ((b^2) - (4*a*c))
                         in (((-1*b) + q)/2,((-1*b) - q)/2)

chineseRemainder (a,m) (b,n) = let ((_,s,t),_) = runWriter $ eGCD (m,n)
                               in (b*s*m + a*t*n) `mod` (m*n)

-- Hanoi with Binary

removeDisk :: Eq disk => disk -> [[disk]] -> [[disk]]
removeDisk = fmap . filter . (/=)

placeDisk :: Ord disk => disk -> [disk] -> Maybe [disk]
placeDisk m [] = Just [m]
placeDisk m (n:ns) = if m < n then Just (m:n:ns) else Nothing

smap :: Monad m => (a -> m a) -> Int -> [a] -> Maybe [m a]
smap  f n ds = if 0 <= n && n < (length ds)
               then let (l,r) = splitAt (n+1) ds
                    in Just $ (fmap pure (init l)) ++ [f (last l)] ++ (fmap pure r)
               else Nothing

hanoiMove :: Ord disk => disk -> Int -> [[disk]] -> Maybe [[disk]]
hanoiMove d n ds = once lifted <|> twice lifted
    where lifted = removeDisk d ds
          moveDisk n = sequence <=< smap (placeDisk d) n
          once = moveDisk ((n+1) `mod` length ds)
          twice = moveDisk ((n+2) `mod` length ds)

diskPosition :: Ord disk => disk -> [[disk]] -> Int
diskPosition d = fst . head . filter (snd) . fmap (second (d`elem`)) . zip [0..]

hanoi :: [Int] -> Maybe [[[Int]]]
hanoi ds = execWriterT $ foldM move startingBoard moves 
  where startingBoard = [ds,[],[]]

        moves = (if odd (length ds) then concat . take 2 . repeat else id)
              . fmap ((!!) ds . countTrailingZeros)
              $ ([1..(2^(length ds)-1)]::[Int])

        move :: [[Int]] -> Int -> ResultLog [[Int]]
        move b d = do
            r <- lift $ hanoiMove d (diskPosition d b) b
            tell [r]
            return r


-- Primality Test

powm :: Int -> Int -> Int -> Int -> Int
powm b 0 m r = r
powm b e m r | e `mod` 2 == 1 = powm (b * b `mod` m) (e `div` 2) m (r * b `mod` m)
powm b e m r = powm (b * b `mod` m) (e `div` 2) m r

powermod b e m = powm b e m 1

bmod (x,n) = ((x+((n-1)`div`2))`mod`n)-((n-1)`div`2)

bseq :: (Int,Int) -> Writer [String] [Int]
bseq (b,n) = let s = countTrailingZeros (n-1)
                 c = shiftL (n-1) s
                 f :: Int -> Writer [String] Int
                 f j = do
                     tell ["b^(2^" ++ show j ++ "*" ++ show c ++ ")"]
                     return $ bmod(powm b (2^(j*c)) n 1,n)
             in do
    sequence $ fmap f [0..(s+1)]

-- Discrete Log
   
primRootTest a m = fmap (\n-> (n, powermod a n m)) [1..(m-2)]

babyStepGiantStep a y n = let s = ceiling $ sqrt (fromIntegral n) 
                              a' = modInv a n
                              f k = let ak = powermod a' k n
                                        as = powermod a s n
                                     in (k, ak, y*ak `mod` n, powermod as k n)
                          in fmap f [0.. (s-1)]

factors n = [x | x <- [1..n], n `mod` x == 0]
is_prime n = factors n == [1, n]
prime_factors n = filter is_prime (factors n)

primRootFactorTest :: Int -> Int -> [Int]              
primRootFactorTest a p = fmap (\d-> powermod a ((p-1) `div` d) p) (prime_factors (p-1))                   
