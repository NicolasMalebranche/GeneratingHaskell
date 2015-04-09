{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor, FlexibleInstances, UndecidableInstances #-}
module ContinuedFraction where

import Data.List
import PowerSeries

data ContinuedFraction a = CF {cfList :: [a] }
	deriving (Functor, Eq)

-- Macht eine Kettenbruchentwicklung
-- floor ist eine Abrundungsroutine
-- isZero entscheidet, ob eine Zahl 0 ist
continuedFraction floor isZero x = CF $ cf x where
	cf x = f : if isZero next then [] else cf $ recip next where
		f = floor x
		next = x - f 

-- Macht einen Bruch aus dem Kettenbruch
--resolveCF :: (Integral a, Fractional b) => ContinuedFraction a -> b
resolveCF = foldr res 0 . cfList where
	res a b = a + recip b

instance Show a => Show (ContinuedFraction a) where
	show = sf 0 . cfList where
		sf i  [] = "|"
		sf i (a:r) | i>30 = ".." 
			| otherwise = show a ++ "|" ++ sf (i+1) r

instance (Num a, Ord a) => Ord (ContinuedFraction a) where
	CF (a:x) <= CF [] = a <= 0
	CF [] <= CF (a:x)= 0 <= a
	CF [] <= CF [] = True
	CF (a:x) <= CF (b:y) = a < b || (a == b && y <= x)


-- Das K von Gauss
cf [] = 0
cf ((a,b):r) = a/(b + cf r)

-----------------------------------------------------------------------------------------
-- Kettenbruchentwicklungen von Potenzreihen

-- Entwicklung der Reihe in einen J-Fraction Kettenbruch 
-- Reihe = mu0/(1+a0*t-t²(mu1/(1+a1*t-t²(..)))
seriesJFraction (Elem mu0 r) =  let
	Elem _ (Elem a0 n) = seriesInvShift $ fmap (/mu0) r
	in (a0,mu0) : seriesJFraction (negate n)

-- Rekonstruiert die Reihe aus dem J-Fraction Kettenbruch
seriesFromJFraction ((a0,mu0):l) = let
	den = Elem a0 $ negate $ seriesFromJFraction l
	in fmap (mu0*) $ seriesInvShift den

-- Entwicklung in einen C-Fraction Kettenbruch
-- Reihe = b0 + a1*t/(1+a2*t/(1+a3*t/1+..))
seriesCFraction (Elem b0 r) = (b0,findOrder 1 r) where
	findOrder i (Elem 0 r) = if i > 50 then [] else findOrder (i+1) r
	findOrder i (Elem a r) = (a,i) : findOrder 1 q where
		Elem _ q = seriesInvShift $ fmap (/a) r 

-- Rekonstruiert die Reihe aus dem C-Fraction Kettenbruch
seriesFromCFraction (b0,l) = Elem b0 $ fro l where
	fro [] = 0
	fro ((a,i):l) = seriesShift (i-1) $ fmap (a*) $ seriesInvShift $ fro l
	

