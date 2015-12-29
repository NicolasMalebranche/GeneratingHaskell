{-# LANGUAGE ParallelListComp #-}
module CyclotomicField where

import Polynomial
import PowerSeries
import PrimeFactors
import Data.MemoTrie

-- Zyklotomische Polynome
cyclotomic n = run 1 1 (seriesGenerating [1,-1]) pf where
	pf = primeFactors n
	run deg s c [] = polyFromSeries (s*deg) $ seriesStretch s c
	run deg s c ((a,m):r) = run (deg*(a-1)) (s*a^(m-1)) newc r where
		newc = seriesStretch a c * seriesInv c

cyclotomicMemo :: Num a => Integer -> Polynomial a
cyclotomicMemo = fmap fromInteger . memo cyclotomic

data CyclotomicField a = Cyc Integer (Polynomial a) deriving Show

-- primitive r-te Einheitswurzel
cycRoot r = Cyc r x

cycRebase (Cyc r p) = let 
	gcd' 1 _ = 1 
	gcd' a b = gcd a b
	fa = foldr gcd' r [ i | (i,a) <- zip [0..] $ polyToList p, a/=0]
	in if fa > 1 then 	Cyc (r`div` fa) $ polyStretch (2-fa) p
	else Cyc r p

cycReduce (Cyc r p@(Polynomial d s)) = let
	eq = cyclotomicMemo r
	red d s = if d<deg eq then s else red (d-1) $ s - 
		seriesShift (d-deg eq) (fmap (seriesCoeff s d*) $ ser eq)
	in Cyc r $ polyClean $ Polynomial (deg eq) $ red d s

-- Bringt eine Zahl auf Normalform
cycClean cy = cycRebase $ cycReduce cy

-- Komplexe Konjugation
cycConjugate (Cyc r p) = con  where
	con = Cyc r $ polyReverse $ Polynomial r (ser p)

instance (Eq a, Num a) => Eq (CyclotomicField a) where
	x==y = cycClean x == cycClean y

instance (Eq a, Num a) => Num (CyclotomicField a) where
	Cyc r p + Cyc r' p' = Cyc r'' $ polyStretch a p + polyStretch b p'
		where [r'',a,b] = map (div (lcm r r')) [1,r,r']
	negate (Cyc r p) = Cyc r $ negate p
	Cyc r p * Cyc r' p' = cycClean $ Cyc r'' $ polyStretch a p * polyStretch b p'
		where [r'',a,b] = map (div (lcm r r')) [1,r,r']
	fromInteger n = Cyc 1 $ fromInteger n
	abs p = undefined 
	signum = undefined
