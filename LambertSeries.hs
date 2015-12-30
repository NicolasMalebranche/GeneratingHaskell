{-# LANGUAGE DeriveFunctor  #-}
module LambertSeries where

import PowerSeries
import DirichletSeries

newtype LambertSeries a = Lambert (PowerSeries a) deriving Functor

lambertFromList l = Lambert $ seriesGenerating l
lambertToList (Lambert s) = seriesToList s

lambertFromSeries s@(Elem c _) = Lambert $ seriesGenerating $ c : l where
	l = map (moebiusInversion $ seriesCoeff s) [1..]

lambertToSeries (Lambert (Elem a l)) = Elem a $ seriesShiftedSum sx where
	coeff = seriesToList l
	sx = [fmap (c*) $ seriesStretch n seriesGeo | (n,c) <- zip [1..] coeff]

-- p(t) = product [ (1-t^k)^a_k, k = [1..]]
seriesAsLambertProduct p = let
	difflog = seriesShift 1 $ seriesDiff p * seriesInv p
	blist = tail $ lambertToList $ lambertFromSeries difflog
	in [ -b /fromIntegral n | (n,b) <- zip [1..] blist]	


instance (Num a) => Num (LambertSeries a) where
	(Lambert a) + (Lambert b) = Lambert (a+b)
	(Lambert a) - (Lambert b) = Lambert (a-b)
	a*b = lambertFromSeries $ lambertToSeries a * lambertToSeries b
	negate = fmap negate
	abs = fmap abs
	signum = fmap signum
	fromInteger i = Lambert $ fromInteger i



instance (Show a) => Show (LambertSeries a) where
	show (Lambert r) = let
		maxdeg = 20
		xpower i = if i == 0 then "" else if i== 1 then "t" else "%^" ++ show i
		showelem i a = if elem sa ["0","0.0","-0.0","0 % 1"] then "" else showsig ++ xpower i where
			sa = show a
			ska = if elem ' ' sa || elem '+' sa then "("++sa++")" else sa 
			showsig = if head ska == '-' then " - "++shown (tail ska) else " + "++shown ska
			shown a = if a=="1" || a=="1.0" then if i == 0 then "1" else "" else a
		s i (Elem a r) = if i == maxdeg then " + O(" ++ xpower maxdeg ++ ")" else
			showelem i a ++ s (i+1) r
		string = s 0 r 
		in (if string!!1 == '+'then "" else "-") ++  drop 3 string
