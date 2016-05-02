module Zeckendorf where

import Data.MemoTrie
import Data.List
import System.IO.Unsafe
import Data.IORef

-- Darstellung ganzer Zahlen mit (Nega-)Fibonaccis
data Zeckendorf = Zecken {zahl::Integer, zeck::[Int]} deriving (Eq,Ord)


{-# NOINLINE negaRef #-}
negaRef :: IORef Bool
negaRef = unsafePerformIO $ newIORef False
nega _ = unsafePerformIO $ readIORef negaRef

instance Show Zeckendorf where
	show = show . zahl

instance Num Zeckendorf where
	a+b = zecken $ zahl a + zahl b
	a-b = zecken $ zahl a - zahl b
	a*b = zecken $ zahl a * zahl b
	fromInteger = zecken 
	signum = signum . zecken . zahl 
	abs = abs . zecken . zahl
	
instance Real Zeckendorf where
	toRational = toRational . zahl
	
instance Enum Zeckendorf where
	fromEnum = fromEnum . zahl
	toEnum = zecken . toInteger

instance Integral Zeckendorf where
	toInteger = zahl
	divMod a b = (zecken x,zecken y) where (x,y) = divMod (zahl a) (zahl b)
	quotRem a b = (zecken x,zecken y) where (x,y) = quotRem (zahl a) (zahl b)
	
fibonacci = memo f where
	f :: Int -> Integer	
	f 0 = 0
	f 1 = 1
	f n = if n > 0 
		then fibonacci (n-1) + fibonacci (n-2)
		else fibonacci (n+2) - fibonacci (n+1)

goldenRatio = (1+ sqrt 5) / 2 :: Double


zecken = \ n -> Zecken n (z n) where
	sqrt5 = sqrt 5
	logGoldenRatio = log goldenRatio
	z 0 =  []
	z n = is : z (n-fibonacci is) where
		m = ceiling $ log (fromIntegral (abs n) * sqrt5) / logGoldenRatio
		is = if nega ()
			then if odd m == (n>0) then  - m else 1 - m
			else if fibonacci m > n then (m-1) else m
	
zeckenShift shift a = zecken $ sum $ map (fibonacci .( + shift )) $ zeck a

infixl 8 +*

-- Fibonacci Product
(+*) x y = zecken $ sum [ fibonacci (i+j) | i<-zeck x, j<-zeck y]

-- Was ganz was lustiges
istSpezialMod = let 
	range = map zecken [1..100]
	in \n s -> all ( \r -> zahl (zecken (n*s) +* r - r) `mod` n == 0) range

spezialZahlenMod n = filter (istSpezialMod n)  [0..]

