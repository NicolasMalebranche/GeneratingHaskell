module CyclotomicField where

import Polynomial
import PowerSeries
import DirichletSeries

-- Zyklotomische Polynome
cyclotomic n = Polynomial {deg = eulerPhi n, ser = s} where
	s = foldr ($) 1 [ f m d | (d,c) <- factorizations n, let m = moebius c, m/=0]
	f 1 d p = p - seriesShift d p
	f (-1) d p = q where q = p + seriesShift d q

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
	eq = cyclotomic r
	red d s = if d<deg eq then s else red (d-1) $ s - 
		seriesShift (d-deg eq) (fmap (seriesCoeff s d*) $ ser eq)
	in Cyc r $ polyClean $ Polynomial (deg eq) $ red d s

-- Bringt eine Zahl auf Normalform
cycClean cy = cycRebase $ cycReduce cy

-- Komplexe Konjugation
cycConjugate (Cyc r p) = con  where
	con = Cyc r $ polyReverse $ Polynomial r (ser p)

-- Realteil
cycRealPart (Cyc r p) = sum $ zipWith (*) (map realToFrac $ polyToList p) 
	[ cos(a*fromIntegral k) | k<-[0..]] where a = 2*pi/fromIntegral r

-- Imaginärteil
cycImaginaryPart (Cyc r p)  = sum $ zipWith (*) (map realToFrac $ polyToList p) 
	[ sin(a*fromIntegral k) | k<-[0..]] where a = 2*pi/fromIntegral r

-- komplexe Norm
cycNorm a = sqrt $ cycRealPart $ a * cycConjugate a

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

instance (Eq a, Fractional a) => Fractional (CyclotomicField a) where
	fromRational q = Cyc 1 $ Polynomial 0 $ fromRational q
	recip (Cyc r p) = let
		(g,(x,_)) = polyEuclid p (cyclotomic r)
		s = recip $ head $ polyToList g
		in Cyc r $ fmap (*s) x
