module Zeckendorf where

import Data.MemoTrie
import Data.List
import Data.List.Ordered
import System.IO.Unsafe
import Data.IORef
import PrimeFactors

-- Darstellung ganzer Zahlen mit (Nega-)Fibonaccis
data Zeckendorf = Zecken {zahl::Integer, zeck::[Int]} deriving (Eq,Ord)


{-# NOINLINE negaRef #-}
negaRef :: IORef Bool
negaRef = unsafePerformIO $ newIORef False
nega _ = unsafePerformIO $ readIORef negaRef

instance Show Zeckendorf where
	show = show . zahl

instance Num Zeckendorf where
	a+b = zeckenShift (sh-4) $ zecken $ zahl aa + zahl bb where
		[aa,bb] = map ( zeckenShift (4-sh) ) [a,b]
		sh = minimum $ map (foldr min 0 . zeck) [a,b]
	negate a = negafib $ negate $ zahl a -- sorry
	a*b = negafib $ zahl a * zahl b  -- sorry
	fromInteger = negafib 
	signum = negafib . signum . zahl 
	abs = zecken . abs . zahl
	
instance Real Zeckendorf where
	toRational = toRational . zahl
	
instance Enum Zeckendorf where
	fromEnum = fromEnum . zahl
	toEnum = zecken . toInteger

instance Integral Zeckendorf where
	toInteger = zahl
	divMod a b = (zecken x,zecken y) where (x,y) = divMod (zahl a) (zahl b)
	quotRem a b = (zecken x,zecken y) where (x,y) = quotRem (zahl a) (zahl b)
	
fibonacci = generalFib 0 1
	
lucas = generalFib 2 1

generalFib a b = gen where
	gen = memo g
	g :: Int -> Integer
	g 0 = a 
	g 1 = b
	g n = if n > 0 
		then gen (n-1) + gen (n-2)
		else gen (n+2) - gen (n+1)

goldenRatio = (1+ sqrt 5) / 2 :: Double

combs = alls :: [[Int]] where
	alls = inter 0 [[i] | i<-[0..]] [ (head x + n):x | (x,n)<- cantor alls [2..]]
	cantor (x:a) b = inter 0 [(x,y)|y<-b] $ cantor a b
	inter n (i:j) r = take n r ++ [i] ++ inter (n+1) j (drop n r)

(zecken, negafib) = (zz False , zz True) where
	zz nega n = Zecken n (z nega n) 
	sqrt5 = sqrt 5
	logGoldenRatio = log goldenRatio
	z _ 0 =  []
	z nega n = is : z nega (n-fibonacci is) where
		m = ceiling $ log (fromIntegral (abs n) * sqrt5) / logGoldenRatio
		is = if nega 
			then if odd m == (n>0) then  - m else 1 - m
			else if fibonacci m > n then (m-1) else m
	
zeckenShift shift a = Zecken s m where
	m = map (shift +) $ zeck a
	s = sum $ map fibonacci m

zeckMult n = Zecken 0 $ if n == 0 then [] else list where
	t s = (zahl $ zeckenShift 1 $ zecken $ n*s) `mod` n == 0
	rep = head $ filter t [1..]
	[ r ] = zeck $ zecken rep
	list = map (+ (-r)) $ zeck $ zecken $ rep * n

infixl 8 +*

-- Fibonacci Product
(+*) x y = sum [ zeckenShift i y | i<-zeck x]

-- Was ganz was lustiges
istSpezialMod = let 
	range = map zecken [ 1 .. 100]
	in \n s -> all ( \r -> zahl (zecken (n*s) +* r - r) `mod` n == 0) range

spezialZahlenMod n = filter (istSpezialMod n)  [0..]

spezialNRange s = (unten,oben) where
	unten =  mun 2
	oben = run unten
	run n = if istSpezialMod n s then run (n+1) else n
	mun n = if istSpezialMod n s then n else mun (n+1)
	

