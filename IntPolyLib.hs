{-# LANGUAGE ParallelListComp #-}
module IntPolyLib where

-- Bibliothek fuer ganzzahlige Polynome

import PowerSeries
import Polynomial
import DirichletSeries

-- Zyklotomische Polynome
cyclotomic n = polyFromSeries (fromIntegral $ eulerphi n) res where
	oper 1 k s = s - seriesShift k s
	oper (-1) k s = ww k s where 
		ww 0 p = ww k (p+s)
		ww i (Elem a r) = Elem a $ ww (i-1) r
	oper _ _ s = s
	start = if moebius n == -1 then seriesGeo else if moebius n == 1 then 1-t else 1
	res = foldr ($) start [oper (moebius k) m | (m,k) <- tail $ factorizations n]


-- Pochhammer-Symbole
fallingFactorials :: Num a => [Polynomial a]
fallingFactorials = map (polyFromList.map fromInteger) $ scanl make [1] [1..] where
	make x n = zipWith (\ a b -> a-n*b) (0:x) (x++[0])

risingFactorials :: Num a => [Polynomial a]
risingFactorials = map (polyFromList.map fromInteger) $ scanl make [1] [1..] where
	make x n = zipWith (\ a b -> a+n*b) (0:x) (x++[0])


-- Tschebyscheff-Polynome
tcheb1 = zipWith (-) tcheb2 $ map (polyShift 1) $ 0:tcheb2

tcheb2 = 1 : (2*x) : zipWith op tcheb2 (tail tcheb2) where
	op a b = fmap (2*) (polyShift 1 b) - a

-- Hermite-Polynome
hermites = 1 : x : zipWith3 op [1..] hermites (tail hermites) where
	op n a b = polyShift 1 b - fmap (*n) a

-- Shapiro-Polynome
shapiroP = 1 : zipWith3 op (map (2^) [0..]) shapiroP shapiroQ where
	op n p q = p + polyShift n q
shapiroQ = 1 : zipWith3 op (map (2^) [0..]) shapiroP shapiroQ where
	op n p q = p - polyShift n q
