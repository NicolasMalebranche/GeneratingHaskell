module RationalRoot where

import Data.Ratio
import Polynomial
import PrimeFactors
import Elementary

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
 	

-- Teilen mit Rest modulo einer Primzahl p
polPDivMod p f g = if (gd < 1) then (fmap (*gvi) $ redp f, 0) else dm $ redp f where
	redp = fmap $ flip mod p
	(gd,gv) = polyTop $ redp g
	gvi = fst $ snd $ euclid gv p
	dm f = if fd>=gd then (polyClean $ redp $ d+mon,polyClean$ redp m) else (0,polyClean f) where
		(fd, fv) = polyTop f
		quot = fv*gvi
		mon = polyShift (fd-gd) $ polyFromList [ quot ]
		diff = polyShift (fd-gd) $ fmap (*quot) g
		(d,m) = dm $ redp (f - diff) 

-- Euklidischer Algorithmus mod p
polPEuclid p f g = if deg f < 0 then (pc g, (0,1)) 
	else (gcd, (y - x*d, x)) where
	pc f = polyClean $ fmap (flip mod p) f
	(d,m) = polPDivMod p g f
	(gcd, (x,y)) = polPEuclid p m f


-- Hensel-Lifting. g muß ein einfacher Teiler von f mod p sein
henselLift p f g = let
	(h,err)= polPDivMod p f g
	(gcd,(ss,tt)) = polPEuclid p g h
	gi = fst $ snd $ euclid (head $polyToList gcd) p
	[s,t] = map (fmap (gi*)) [ss,tt]
	lift g h s t = (g,h) : lift g' h' s' t' where
		[g',h',s',t'] = map polyClean [ g+t*e, h+s*e , s-d*s, t-d*t]
		e = f - g*h
		d = s*g' + t*h' - 1
	in 
	if err/=0 then error "henselLift: kein Teiler" else 
	if deg gcd >0 then error "henselLift: kein einfacher Teiler" else 
	lift g h s t




