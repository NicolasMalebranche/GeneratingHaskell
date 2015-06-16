{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor #-}
module GottscheFormula where

-- Computes the generating series of Betti numbers of Hilbert schemes and 
-- generalized Kummer varieties, according to
-- Lothar Göttsche:
-- Hilbert Schemes of Zero-Dimensional Subschemes of Smooth Varieties
-- Springer Lecture Notes in Mathematics 1572
-- pages 49, 35

import PowerSeries
import Polynomial
import Data.Array


-- Input: Betti numbers of the underlying surface
b1 = 4
b2 = 6
b3 = 4

-- Output: Betti numbers of the outcoming generalized Kummer of dim 2n
bettiKummer n =  polyFromSeries (deg c - b1) $ ser c * d where
	c = seriesCoeff kummerseries (n+1)
	d = seriesInv (1+t)^b1

-- And of Hilb^n 
bettiHilbert n = seriesCoeff hilbproduct n


-- Define the awkward multiplication for omega
data Omega a = Om (Array Integer a) deriving (Show,Eq,Functor)

omegaAdd (Om x) (Om y) = let [r,s] = map (snd.bounds) [x,y]
	in Om $ accumArray (+) 0 (0,max r s) $ assocs x ++ assocs y

omegaMult (Om x) (Om y) = let
	gcd' 0 0 = 0
	gcd' n m = gcd n m
	[r,s] = map (snd.bounds) [x,y]
	newass = [(gcd' i j, a*b) | (i,a)<-assocs x, (j,b)<-assocs y]
	in Om $ accumArray (+) 0 (0,max r s) newass
	
omegaPower n = Om $ listArray (0,n) $ [0 |i <- [1..n]] ++ [1]

omegaSet1 (Om x) = sum $ elems x

omegaWDiffWB (Om x) = Om $ listArray (bounds x) $ zipWith (*) (elems x) $ map (fromInteger.(^b1)) [0..]

instance (Num a) => Num (Omega a) where
	(+) = omegaAdd
	(*) = omegaMult
	negate = fmap negate
	abs = fmap abs
	signum = fmap signum
	fromInteger 0 = Om $ listArray (0,-1) []
	fromInteger i = Om $ listArray (0,0) [fromInteger i]

-- Compute the generating series
innerbracket k = fraction where
	fraction = seriesStretch k $ den*num
	den = seriesGenerating[1,x^(2*k-1)]^b1 * seriesGenerating[1,x^(2*k+1)]^b3
	num = seriesGenerating[x^(i*(2*k-2))|i<-[0..]] * seriesGenerating[x^(i*2*k)|i<-[0..]]^b2 * seriesGenerating[x^(i*(2*k+2))|i<-[0..]] 

awkproduct = seriesShiftedProduct [timesOm k $ seriesShift (-k) $ innerbracket k | k<-[1..]] where
	timesOm k = fmap (fmap (\i->fromInteger i* omegaPower k))

kummerseries = fmap (fmap (omegaSet1.omegaWDiffWB)) awkproduct

hilbproduct = seriesShiftedProduct [seriesShift (-k) $ innerbracket k | k<-[1..]]


