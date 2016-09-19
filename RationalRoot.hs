module RationalRoot where

import Data.Ratio
import Polynomial
import PrimeFactors
import Elementary
import System.IO.Unsafe
import System.Random hiding (random)
import Data.Numbers.Primes(primes)

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

-- Distinct degree factorization mod p
-- f muß quadratfrei sein
polPDDF p f = run 1 ( polyClean $ fmap (flip mod p) f) where
	run i f = let 
		g = powerMod (\q-> snd $ polPDivMod p q f) x (p^i) - x
		(gcd,_) = polPEuclid p f g
		(ff,_) = polPDivMod p f gcd
		in 
		if deg f >= 2*i then if deg gcd > 0 then (gcd,i) : run (i+1) ff else run (i+1) f 
		else if deg f == 0 then [] else[(f,deg f)]

-- Cantor-Zassenhaus Algorithmus
-- p muß ungerade Primzahl sein
polPCZ p f d = cz [f] where
	r = deg f `div` d
	random _ = fromIntegral $ unsafePerformIO (getStdRandom (randomR (1,p))) 
	randPoly _ = polyFromList [ random () | _ <- [1.. deg f]]
	cz factors = if fromIntegral (length factors) == r then factors else run factors where
		h = randPoly()
		g = powerMod (\q-> snd $ polPDivMod p q f) h (div (p^d-1) 2) - 1
		run [] = []
		run (u:factors) = (if deg u > d && deg gcd > 0 && deg gcd < deg u then [gcd,co] else [u]) ++ run factors where
			(gcd, _) = polPEuclid p g u
			(co,_) = polPDivMod p u gcd

-- Faktorisiert mod p>2
-- f muß quadratfrei sein mod p
polPFactor p f = [ h| (g,d) <- polPDDF p f, h <- polPCZ p g d]

-- Faktorisiert ein Polynom über den ganzen Zahlen in irreduzible
-- Komponenten vermöge des Zassenhaus Algorithmus
poliFactor ff = if deg f < 2 then [(f,1)] else [(fj,i) | (g,i) <- zip squarefree [1..], fj<- factor g] where
	f = polyClean ff	
	squarefree = map poli $ polySquareFree $ fmap fromIntegral f
	factor f = undefined where
		b = max (abs $ snd $ polyTop f)(abs $ snd $ polyLowest f)
		a = head [ i-1 | i<-[1..] , p^i > 2*b ]
		p = head [ p |p <- primes, let (gcd,_) = polPEuclid p f (polyDiff f), deg gcd == 1]
		


-- Hensel-Lifting. g muß ein einfacher Teiler von f mod p sein
henselLift p f g = let
	(hh,err)= polPDivMod p f g
	h = modp h
	modp f = fmap (neg . flip mod p) f where neg x = if 2*x > p then x-p else x
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




