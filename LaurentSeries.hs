{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor #-}
module LaurentSeries where

import Data.List
import PowerSeries
import Data.IORef
import System.IO.Unsafe

-- Präzisions-Potenz für Laurentreihen. Braucht man zum Invertieren.
laurentPrecRef = unsafePerformIO $ newIORef 60
laurentReadPrec _ = unsafePerformIO $ readIORef laurentPrecRef 
laurentWritePrec = unsafePerformIO . writeIORef laurentPrecRef 

-- Laurentreihen mit endlichem Hauptteil
-- Der ganzzahlige Parameter ist üblicherweise negativ
-- Die Reihe will gelesen werden als Lau r f = x^r f
data LaurentSeries a = Lau Integer (PowerSeries a)
	deriving (Functor)

-- Addition zweier Laurentreihen
laurentAdd (Lau r p) (Lau r' p') = add where 
	add = if r<=r' then Lau r (p + seriesShift (r'-r) p') else Lau r' (seriesShift (r-r') p + p') 

-- Multiplikation zweier Laurentreihen
laurentMult (Lau r p) (Lau r' p') = Lau (r+r') $ seriesMult p p'

-- Putzt negative Exponenten mit Koeffizient 0 weg
laurentClean (Lau r (Elem a p)) = if r<0 && a == 0 
	then laurentClean (Lau (r+1) p) else Lau r (Elem a p)

-- Bestimmt den kleinsten Exponenten, dessen Koeffizient nicht 0 ist und korrigiert entsprechend
-- Gibt Nothing zurück, wenn die Reihe 0 zu sein scheint
laurentOrder (Lau r p) = lo r p where
	bound = laurentReadPrec ()
	lo i (Elem a p) = if a /= 0 then Just $ Lau i $ Elem a p
		else if i > bound then Nothing else lo (i+1) p

-- Invertiert eine Laurentreihe.
-- Entscheidet, ob eine Reihe 0 ist durch Auswerten der ersten laurentPrec Glieder
laurentInv l = case laurentOrder l of
	(Just (Lau r p)) -> Lau (-r) $ seriesInv p
	Nothing -> error $ "Laurent series division by zero (up to precision: x^" ++
		show (laurentReadPrec ()) ++ ")"

-- Differential
laurentDiff (Lau r p) = let
	d i (Elem a ar) = Elem (i*a) $ d (i+1) ar
	in laurentClean $ Lau (r-1) $ d r p

-- Multipliziert mit x^n
laurentShift n (Lau r p) = Lau (r+n) p 

-- Schneidet oben ab. Reihe wird Laurentpolynom vom Grad n-1
laurentCutDegree n (Lau r p) = Lau r $ seriesCutDegree (n-r) p

-- Schneidet unten ab. Reihe geht mit x^n los.
laurentCutOrder n (Lau r p) = Lau neworder $ cut (neworder-r) p where
	neworder = max n r
	cut 0 p = p
	cut n (Elem a ap) = cut (n-1) ap

-- Bestimmt das Residuum
laurentResidue (Lau r p) = lr r p where
	lr r (Elem a p) | r < -1 = lr (r+1) p
		| r == -1 = a
		| r > -1 = 0

-- Bestimmt den konstanten Term
laurentConstantTerm (Lau r p) = ct r p where
	ct r (Elem a p) | r < 0 = ct (r+1) p
		| r == 0 = a
		| r > 0 = 0

-- Bestimmt den Nebenteil
laurentIrrelevant (Lau r p) = li r p where
	li r ap@(Elem a p) | r < 0 = li (r+1) ap
		| r ==0 = ap
		| r > 0 = li (r-1) $ Elem 0 $ Elem a p

-- Extrahiert Koeffizienten aus einem bestimmten Bereich
laurentExtract from to (Lau r ser) = extr from ser where
	extr i s@(Elem a b) | i < r  = 0:extr(i+1) s
		| i >= to = []
		| otherwise = a: extr(i+1) b

instance (Num a) => Num (LaurentSeries a) where
	(+) = laurentAdd
	negate = fmap negate
	abs = fmap abs
	signum = fmap signum
	fromInteger = Lau 0 . fromInteger
	(*) = laurentMult

instance (Fractional a, Eq a) => Fractional (LaurentSeries a) where
	fromRational a = Lau 0 $ fromRational a
	recip l = case laurentOrder l of
		(Just (Lau r p)) -> Lau (-r) $ recip p
		Nothing -> error "division by zero"

instance (Eq a, Num a) => Eq (LaurentSeries a) where
	a == b = case laurentOrder (a-b) of
		Nothing -> True
		Just _ -> False

instance (Num a, Show a, Ord a) => Show (LaurentSeries a) where
	show (Lau hr r) = let
		maxdeg = 20
		xpower i = if i == 0 then "" else if i== 1 then "x" else "x^" ++ show i
		showelem i a = if a == 0 then "" else showsig ++ showa ++ xpower i where
			showsig = if a <0 then " - " else " + "
			showa = if abs a == 1 then if i == 0 then "1" else "" else show (abs a)
		s i (Elem a r) = if i+hr == maxdeg then " + O(" ++ xpower maxdeg ++ ")" else
			showelem (i+hr) a ++ s (i+1) r
		string = s 0 r 
		in (if string!!1 == '+'then "" else "-") ++  drop 3 string