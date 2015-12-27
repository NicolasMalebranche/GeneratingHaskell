
module FactorialNumber where

import Data.List
import PAdic

-- FN x == sum [ (i+1)! * x[i] | i<-[0..]]
-- Funktioniert auch mit unendlich langen Listen
newtype FactorialNumber = FN [Int] 

-- Korrigiert Digits, die nicht im vorgesehenen Bereich liegen
fnClean (FN x) = FN $ fc 2 0 x where
	fc i u (a:b) = m : fc (i+1) d b where (d,m) = divMod (a+u) i
	fc i 0 [] = []
	fc i u [] = fc i u [0]

-- Dasselbe mit Integer-wertigen Listen
fnClean' x = FN $ fc 2 0 x where 
	fc i u (a:b) = fromInteger m : fc (i+1) d b 
		where (d,m) = divMod (a+u) i
	fc i 0 [] = []
	fc i u [] = fc i u [0]

-- Zip-Funktion
fnZip f (FN x) (FN []) = FN $ map (flip f 0) x
fnZip f (FN []) (FN y) = FN $ map (f 0) y
fnZip f (FN (a:r)) (FN (b:q)) = FN $ f a b : z 
	where FN z = fnZip f (FN r) (FN q)

-- Wertet die Teilsummen aus. Konvergiert gegen die Zahl.
fnToSequence (FN x) = ts 0 1 2 x  where
	ts acc _ _ [] = repeat acc
	ts acc fac i (a:r) = nacc : ts nacc (fac*i) (i+1) r
		where nacc = acc + toInteger a*fac

-- Konvertiert in eine p-adische Zahl
fnToPAdic (FN x) = fp $ 0 : zipWith ((*).toInteger) x facs' where
	fp [] = 0
	fp y = Z_p a $ r + fp d where
		(t,d) = splitAt (p()) y
		Z_p a r = fromInteger $ sum t
	facs' = 1 : [ f*(if m==0 then d else i)| 
		(i,f)<-zip [2..] facs', let (d,m) = i `divMod` p()]

-- Interpretiert eine faktorielle Zahl als Lehmer-Code (rückwärts gelesen)
fnPermute (FN x) a = f [] 0 (0:x) a where
	f l n [] a = l ++ a
	f l n x [] = l
	f l n (i:r) (a:b) = f (t ++ a:d) (n+1) r b where
		(t,d) = splitAt (n-i) $ l

-- Kann Gleichheit nur für endliche Zahlen entscheiden
instance Eq FactorialNumber where
	a==b = compare a b == EQ

instance Ord FactorialNumber where 
	compare (FN x) (FN y) = c x y where
		c (a:r) (b:q) = case compare a b of
			{EQ -> c r q;  other -> other}
		c (a:r) [] = if a>0 then GT else c r []
		c [] (b:q) = if b>0 then LT else c [] q
		c [][] = EQ

instance Num FactorialNumber where
	a@(FN x) * b@(FN y) = let
		e = zipWith ((*).toInteger) x $ fnToSequence b
		f = zipWith ((*).toInteger) y $ 0:fnToSequence a
		in fnClean' e + fnClean' f
	a + b = fnClean $ fnZip (+) a b
	a - b = fnClean $ fnZip (-) a b
	negate (FN x) = fnClean $ FN $ map negate x
	fromInteger n = FN $ fI 2 n where 
		fI i 0 = []
		fI i n = fromInteger m : fI (i+1) d where (d,m) = divMod n i
	abs = id
	signum = undefined

instance Show FactorialNumber where
	show (FN []) = "0"
	show (FN r) = ps 0 r "" where
		maxDigits = 19
		sh i r = ((['0'..'9'] ++ ['a'..'z']) !! i) : r
		ps i [] a = a
		ps i (x:r) a = if i > maxDigits then ".."++a else ps (i+1) r (sh x a)