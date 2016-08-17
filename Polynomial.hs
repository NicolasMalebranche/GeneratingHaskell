{-# LANGUAGE MultiParamTypeClasses, DeriveFunctor, FlexibleInstances, OverlappingInstances, IncoherentInstances #-}
module Polynomial where

import PowerSeries

-- Polynome sind Potenzreihen, deren maximaler Grad bekannt ist
-- Das Nullpolynom hat negativen Grad
data Polynomial a = Polynomial {deg::Integer, ser::PowerSeries a} deriving Functor


-- das Monom x
x :: (Num a) => Polynomial a
x = Polynomial 1 $ Elem 0 $ Elem 1 0

-- konstantes Polynom
polyConst a = Polynomial 0 $ Elem a 0

-- Macht den Grad richtig
polyClean p = Polynomial {deg = d, ser = ser p} where
	d = findDegree (-1) 0 $ ser p
	findDegree ad i (Elem a ar) = if i > deg p then ad else
		if a/= 0 then findDegree i (i+1) ar else findDegree ad (i+1) ar 

-- Baut ein Polynom aus einer (endlichen) Liste
polyFromList l = Polynomial {deg = fromIntegral $ length l - 1, 
	ser = seriesGenerating l}

polyToList p = take (fromIntegral $ deg p + 1) $ seriesToList $ ser p

-- Baut ein Polynom vom Grad d durch Abschneiden einer Reihe
polyFromSeries d s = Polynomial { deg = d, ser = seriesCutDegree (d+1) s}

-- Faltung von unten (= links)
polyFoldB op init p = fol 0 init $ ser p where
	fol i val (Elem a ar) = if i > deg p then val else
		fol (i+1) (op val a) ar

-- Faltung von oben, vom Topgrad (= rechts)
polyFoldT op init p = fol 0 $ ser p where
	fol i (Elem a ar) = if i > deg p then init else
		op a $ fol (i+1) ar

-- bestimmt den Koeffizienten niedrigster Ordnung
polyLowest p = pl 0 $ ser p where
	pl i (Elem a ar) = if a/=0 then (i,a) else if i > deg p then (i,0) else
		pl (i+1) ar

-- bestimmt den Koeffizienten höchster Ordnung
polyTop p = polyFoldT pt (-1, 0) p where
	pt a (i, 0) = (0, a)
	pt a (i, r) = (i+1, r)

-- Differential
polyDiff p = Polynomial {deg = deg p - 1, ser = seriesDiff $ ser p}

-- Setzt ein Argument ein
polyEval p x = eval 0 $ ser p where
	eval i (Elem a ar) = if i>deg p then 0 else a + x * eval (i+1) ar
instance Num a => Composeable (Polynomial a) a a where
	(°) = polyEval

-- Setzt eine Potenzreihe ein
seriesInPoly p (Elem c r) = Elem (cc + polyEval p c) cr where
	co rpower (Elem a ar) = fmap (a*) rpower + Elem 0 (co (rpower*r) ar)
	Elem cc cr = co 1 $ ser p
instance Num a => Composeable (Polynomial a)(PowerSeries a)(PowerSeries a) where
	(°) = seriesInPoly

-- Setzt ein anderes Polynom ein
polyComp p q = Polynomial {deg = deg p * deg q, ser = seriesInPoly p $ ser q} 
instance Num a => Composeable (Polynomial a)(Polynomial a)(Polynomial a) where
	(°) = polyComp

-- p(x) -> x^d p(1/x). Achtung: nimmt den gespeicherten Grad. Der tatsächliche
-- Grad kann kleiner sein. In diesem Fall polyClean vorschalten!
polyReverse p = Polynomial {deg = deg p, ser = rev 0 0 $ ser p} where
	rev i s (Elem a ar) = if i > deg p then s else rev (i+1) (Elem a s) ar 

-- Multipliziert mit x^n. Falls n<0, killt die Terme mit negativen Exponenten.
polyShift n p = Polynomial {deg = deg p + n, ser = seriesShift n $ ser p }

-- Setzt x^n ein, wenn n>0.
-- Wenn n<0, nimmt nur jeden (2-n)-ten Koeffizient
polyStretch n p = if n>0 
	then Polynomial {deg = deg p * n, ser = ss (ser p) }
	else Polynomial {deg = deg p `div` (2-n), ser =  nn (ser p) }
	where
	ss (Elem a ar) = Elem a $ seriesShift (n-1) $ ss ar
	nn (Elem a ar) = Elem a $ nn $ seriesShift (n-1) ar

-- Teilen mit Rest. Koeffizientenbereich muß ein diskreter Körper sein.
polyDivMod p q = if (qd < 1) then (fmap (/qv) p, 0) else dm p where
	(qd, qv) = polyTop q
	dm p = if pd>=qd then (d+mon,m) else (0,polyClean p) where
		(pd, pv) = polyTop p
		quot = pv/qv
		mon = polyShift (pd-qd) $ Polynomial 0 $ Elem quot 0
		diff = polyShift (pd-qd) $ fmap (*(pv/qv)) q
		(d,m) = dm (p - diff) 

-- Euklidischer Algorithmus. Findet größten gemeinsamen Teiler.
polyGCD p q = if deg m < 0 then q else polyGCD q m where
	(d,m) = polyDivMod p q

-- polyEuclid p q = (g,(x,y)) 
-- ==> g= x*p + y*q
polyEuclid p q = if deg p < 0 then (q, (0,1)) 
	else (gcd, (y - x*d, x)) where
	(d,m) = polyDivMod q p
	(gcd, (x,y)) = polyEuclid m p


-- Setzt das negative Argument ein
polyCompNegate p = Polynomial { deg = deg p, ser = seriesCompNegate $ ser p}

instance (Num a) => Num (Polynomial a) where
	p + q = Polynomial {deg = max (deg p) (deg q), ser = ser p + ser q}
	p * q = Polynomial {deg = deg p + deg q, ser = ser p * ser q}
	negate = fmap negate 
	abs = fmap abs
	signum = fmap signum
	fromInteger i = Polynomial { deg = if i==0 then -1 else 0, ser = fromInteger i}

instance (Eq a) => Eq (Polynomial a) where 
	p == q = isEq 0 (ser p) (ser q) where
		bound = (max (deg p) (deg q))
		isEq i (Elem a ar) (Elem b br) = 
			if i > bound then True else a==b && isEq (i+1) ar br

instance (Ord a) => Ord (Polynomial a) where
	compare p q = compare (polyToList p) (polyToList q) 

instance (Show a) => Show (Polynomial a) where
	show p = let
		xpower i = if i == 0 then "" else if i== 1 then "x" else "x^" ++ show i
		showelem i a = if elem sa ["0","0.0","-0.0"] then "" else showsig ++ xpower i where
			sa = show a
			ska = if elem ' ' sa || elem '+' sa then "("++sa++")" else sa 
			showsig = if head ska == '-' then " - "++shown (tail ska) else " + "++shown ska
			shown a = if a=="1" || a=="1.0" then if i == 0 then "1" else "" else a
		s i (Elem a r) = if i > deg p then "" else
			showelem i a ++ s (i+1) r
		string = s 0 (ser p) 
		in if string == "" then "0" else (if string!!1 == '+'then "" else "-") ++  drop 3 string
