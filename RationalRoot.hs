module RationalRoot where

import Data.Ratio
import Polynomial
import PrimeFactors

-- Alle rationalen Nullstellen eines rationalen Polynoms
-- Der letzte Eintrag ist der verbleibende Faktor
rationalRoots :: Polynomial Rational -> [Polynomial Rational]
rationalRoots p = let
	(deg,top) = polyTop p
	(ord,low) = polyLowest p
	(z,n) = (allFactors $ numerator (top/low), allFactors $ denominator (top/low))
	tests = if low==0 then [] else  [ s*r2%r1 | r1<- z, r2<- n, s <- [1,-1]]
	f [] = [p]
	f (a:r) = if polyEval p a == 0 then t : rationalRoots(fst $ polyDivMod p t) else f r where t = polyFromList [1,-recip a]
	in if ord > 0 then x : rationalRoots (fst $ polyDivMod p x) else f tests

-- Größter gemeinsamer Teiler der Koeffizienten eines Polynoms
poliContent = polyFoldT gcd 0

-- Liefert ein Vielfaches des Polynoms mit Content 1
poli :: Polynomial Rational -> Polynomial Integer
poli r = fmap (flip div $ poliContent rb) rb where
	hn = fromInteger $ polyFoldT (lcm . denominator) 1 r
	rb = fmap (numerator .(hn*)) r

poliGCD :: Polynomial Integer -> Polynomial Integer -> Polynomial Integer
poliGCD a b = fmap (gcd ga gb*) (poli g) where  
	[ga,gb] = map poliContent [a,b]
	g = polyGCD (fmap (%1) a) (fmap (%1) b)
 	
