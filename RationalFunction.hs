{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor #-}
module RationalFunction where

import PowerSeries
import Polynomial
import LaurentSeries
import Data.Ratio

-- Bruchstrich, geringere Priorität als + oder -
infixl 5 //
(//):: Integral a => Polynomial a -> Polynomial a -> RationalFunction (Ratio a)
p // q = Rat (fmap fromIntegral p) (fmap fromIntegral q)

-- Rationale Funktionen
data RationalFunction a = Rat {
	num :: Polynomial a, den :: Polynomial a 
	} deriving (Functor)

-- Kürzt mit x^n
ratReduceMon r@(Rat p q) = if red>0 then 
	Rat (polyShift (-red) p) (polyShift (-red) q) else r where
		(lp,_) = polyLowest p
		(lq,_) = polyLowest q
		red = min lp lq

-- Hebt hebbare Singularitäten
ratReduce r@(Rat p q) = if deg d < 1 then r else Rat (red p) (red q) where
	d = polyGCD p q 
	red p = fst $ polyDivMod p d

-- erweitert auf Rationale Skalare
ratToRational :: (Integral a) => RationalFunction a -> RationalFunction (Ratio a)
ratToRational = fmap fromIntegral

-- Kürzt alle Skalarnenner raus
ratToIntegral r@(Rat p q) = let  
	op r (a,b) = (gcd a $ numerator r, lcm b $ denominator r)
	(a,b) = polyFoldT op (0,1) p
	(c,d) = polyFoldT op (0,1) q
	mult = lcm b d % gcd a c
	sign r@(Rat _ (Polynomial _ (Elem b _))) = 
		if signum b < 0 then fmap negate r else r
	in sign $ fmap (numerator . (*) mult) r

-- Vereinfacht den Bruch soweit als möglich.
ratReduceInt :: Integral a => RationalFunction a -> RationalFunction a
ratReduceInt = ratToIntegral . ratReduce . ratToRational 

-- Entwickelt die rationale Funktion in eine Laurentreihe
ratMakeLaurent (Rat p q) = Lau 0 (ser p) / Lau 0 (ser q) 

-- Wendet die Transformation x -> 1/x an (Auswertung bei unendlich)
ratAntipode (Rat p q) = res where
	res = Rat (polyShift (m - dp) rp) (polyShift (m - dq) rq)
	(dp, dq) = (deg p, deg q)
	(m, rp, rq) = (max dp dq, polyReverse p, polyReverse q)

instance (Eq a, Num a) => Eq (RationalFunction a) where
	Rat a b == Rat c d = a*d == b*c

instance (Num a) => Num (RationalFunction a) where
	Rat p q * Rat pp qq = Rat (p*pp) (q*qq)
	Rat p q + Rat pp qq  = Rat (p*qq+pp*q) (q*qq)
	negate (Rat p q) = Rat (negate p) q
	abs = fmap abs
	signum = fmap signum
	fromInteger i = Rat (fromInteger i) 1

instance (Num a) => Fractional (RationalFunction a) where
	fromRational r = Rat (fromInteger $ numerator r) (fromInteger $ denominator r)
	Rat p q / Rat pp qq = Rat (p*qq) (q*pp)
	recip (Rat p q) = Rat q p

instance (Num a, Show a, Ord a) => Show (RationalFunction a) where
	show (Rat p q) = (if lp > 0 then "{ "++show p++" }" else show p) ++
		" % "++ if lq > 0 then "{ "++show q++" }" else show q where
			(lp,_) = polyTop p
			(lq,_) = polyTop q
