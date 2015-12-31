{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor, FlexibleInstances #-}

-- Modul für p-adische Zahlen
module PAdic where

import System.IO.Unsafe
import Data.IORef
import Data.Ratio
import ContinuedFraction

-- Datentyp für Ziffern. Sollte p^2 noch enthalten
type Digit = Int

-- p, als globale Variable. Voreinstellung ist 2
{-# NOINLINE pRef #-}
pRef :: IORef Digit
pRef = unsafePerformIO $ newIORef 2
p _ = fromIntegral $ unsafePerformIO $ readIORef pRef
-----------------------------------------------------------------------------------------

-- Division mit Rest modulo p
divMod_p :: Integral a => a -> (a,Digit)
divMod_p k = (d,fromIntegral m) where (d,m) = divMod k $ p()

div_p k = k `div` p()
mod_p k = fromIntegral $ k `mod`  p() :: Digit

-- Binomialkoeffizient
choose n k = a 1 1 where
	bd = if n > 2*k then k else n-k
	a i acc = if i > bd then acc else a (i+1) $ acc*(n-bd+i) `div` i

-- Rationale Approximation von c mit Modulus m
-- https://www.cs.drexel.edu/~jjohnson/2012-13/fall/cs300/resources/p2-wang.pdf
rationalApproximation c m = rc (0,m) (1,c) where
	rc (u2,u3) (v2,v3) = let (q,r) = divMod u3 v3 in
		if m > 2*v3^2 then v3%v2 else
		rc (v2,v3) (u2-q*v2,r)

-----------------------------------------------------------------------------------------

-- Datentyp für Z_p über einer Zahl p
data Z_p = Z_p Digit Z_p

-- Übertrag 
carry_p = c 0 where c a (Z_p i r) = Z_p m $ c d r where (d,m) = divMod_p (a+i) 

-- Erweiterter Euklidischer Algorithmus
euclid 0 b = (b, (0, 1))
euclid a b = (gcd, (y - x*d, x)) where
	(d,m) = divMod b a
	(gcd, (x, y)) = euclid m a

-- Zählt p-Potenzen in einer Zahl
-- Achtung! Terminiert nicht, wenn 0 eingegeben wird
order_p i = if m==0 then 1+order_p d else 0 where 
	(d,m) = divMod_p i

-- orderRem_p n = (o,r) wobei n==(p^o)*r und o maximal
-- Achtung! Terminiert nicht, wenn 0 eingegeben wird
orderRem_p :: (Integral i,Integral j) => i -> (j,i)
orderRem_p = c 0 where c o n = if m==0 then c (o+1) d else (o,n) where (d,m) = divMod_p n

-- Inverses modulo p
invMod_p n = if gcd == 1 then mod_p x else error $"not invertible mod "++show (p()) where
		(gcd,(x,_)) = euclid (mod_p n) $ p() ;

-- Wurzel modulo p, einfach durch Ausprobieren
sqrtMod_p n = f 0 where 
	pp=p()
	f i = if mod(i^2 - n) pp == 0 then i else if i<pp then f (i+1) else
		error $ show n++" admits no sqrt mod "++show pp

-- Multipliziert mit p^k in Z_p. Schneidet Ziffern ab, falls k < 0
shiftZ_p k = if k < 0 then left k else right k where
	right k z = if k==0 then z else Z_p 0 $ right (k-1) z
	left k (Z_p _ r) = if k== -1 then r else left (k+1) r

-- Multipliziert eine Z_p Zahl mit einem Skalar s
multZ_p s = c 0 where c u (Z_p a r) = Z_p m$c d r where (d,m)=divMod_p$ s*fromIntegral a+u

-- Inverses einer ganzen Zahl in Z_p
invZ_p a = d 1 where
	a' = invMod_p a ; pp = p()
	d c = Z_p (fromIntegral t) $ d $ div (c-a*t) pp where t = mod (c*a') pp

-- Schneidet (max. 8) führende Nullen ab
estimateOrderZ_p = e 0 where e i z@(Z_p a r) = if i>7 || a/=0 then (i,z) else e (i+1) r

-- (a,b) = splitAtZ_p k p bedeutet p = a + p^k * b
splitAtZ_p k q@(Z_p c x) = if k<1 then (0,q) 
	else (a*p() + fromIntegral c , b) where
	(a,b) = splitAtZ_p (k-1) x

instance Num Z_p where
	fromInteger i = Z_p m $ fromInteger d  where (d,m)= divMod_p i
	(+) = c 0 where c u (Z_p a x)(Z_p b y) = Z_p m $c d x y where (d,m)= divMod_p (u+a+b)
	(-) = c 0 where c u (Z_p a x)(Z_p b y) = Z_p m $c d x y where (d,m)= divMod_p (u+a-b)
	signum (Z_p a r) = if a==0 then 0 else rtUnityZ_p a
	abs (Z_p a _) = if a==0 then undefined else 1
	-- Achtung! Es wird nur einmal Übertrag gemacht.
	(*) (Z_p afst arst) = carry_p . f facc arst where
		f acc ale br = Z_p (acc br) $ f newacc ar br where
			Z_p a ar = ale
			newacc (Z_p b rb) = a*b + acc rb
		facc (Z_p b rb) = afst*b

instance Fractional Z_p where
	Z_p 0 rC / Z_p 0 rA = rC/rA
	Z_p c rC / Z_p a rA = bb where
		a' = invMod_p a
		d c = Z_p t $ d $ div_p (c-a*t) where t = mod_p(c*a')
		b = mod_p (c*a')
		r = Z_p (div_p (c-a*b)) 0
		bb = Z_p b $ d 1 * (r + rC - rA*bb)
	fromRational r = d $ numerator r where
		a = denominator r
		a' = fromIntegral $ invMod_p a
		d c = Z_p (fromIntegral b) $ d $ div_p (c-a*b) where 
			b = mod (c*a') $ p()

instance Eq Z_p where 
	a == b = Q_p 0 a == Q_p 0 b
instance Ord Z_p  where -- Das muss leider sein, damit 
	-- die Real-Instanz definierbar wird
	compare a b = compare (Q_p 0 a) (Q_p 0 b)
instance Real Z_p where
	toRational z = create 0 1 z 0 where
		create n m (Z_p a r) c = 
			if n > q_pPrec then rationalApproximation c m
			else create (n+1) (p()*m) r $! c+fromIntegral a*m

-- Setzt p^o * r, r eine Z_p-Zahl in eine exp-artige Reihe ein
inExpSeriesZ_p coeffs (o,r) = if (p()-1)*o<=1 then error "series not convergent" else f 1 0 1 coeffs where
	f n sh rp (c:co) = summand + shiftZ_p si (invZ_p rem *f (n+1)(sh+ds)(rp*r) co) where
		summand = shiftZ_p sh $ multZ_p c rp
		(z,rem) = orderRem_p n
		si = if n `mod` (p()-1) == 0 then o-1 else o
		ds = o-si-z
		
-- Setzt p^o * r, r eine Z_p-Zahl in eine log-artige Reihe ein
inLogSeriesZ_p coeffs (o,r) = if o<1 then error "series not convergent" else shiftZ_p o $f 1 0 r coeffs where
	f n sh rp (c:co) = summand + shiftZ_p si (f (n+1) (sh+o-si) (rp*r) co) where
		summand = shiftZ_p (sh-z) $ multZ_p c rp * invZ_p rem
		(z,rem) = orderRem_p n
		si = if rn == 1 then o-1 else o where (_,rn) = orderRem_p n

-- Achtung: für Werte, wo die Funktionen nicht definiert sind, terminieren sie evtl. nicht
instance Floating Z_p where
	pi = 0
	exp = inExpSeriesZ_p (repeat (1::Digit)) . estimateOrderZ_p
	sin = inExpSeriesZ_p (cycle [0,1,0,-1::Digit]) . estimateOrderZ_p
	cos = inExpSeriesZ_p (cycle [1,0,-1,0::Digit]) . estimateOrderZ_p
	sinh = inExpSeriesZ_p (cycle [0,1::Digit]) . estimateOrderZ_p
	cosh = inExpSeriesZ_p (cycle [1,0::Digit]) . estimateOrderZ_p
	asinh x = log $ x + sqrt(x^2+1)
	acosh x = log $ x + sqrt(x^2-1)
	atanh x = log ((1+x)/(1-x)) / 2
	asin x = pi/2 - acos x
	acos x = multZ_p 2 $ atan (sqrt ((1-x)/(1+x)) )
	log = l.f where
		f (Z_p 0 r) = f r; f r = r
		l x = inLogSeriesZ_p (cycle [1,-1::Digit])$ estimateOrderZ_p $ x/signum x - 1
	sqrt x= if p()==2 then sq2 x else sqp x where
		sq2 (Z_p 0 (Z_p 0 x)) = Z_p 0 $ sq2 x
		sq2 (Z_p 1 (Z_p 0 (Z_p 0 (Z_p x0 x1)))) = w where
			y0 = if odd x0 then 1 else 0
			y1 = if y0 == 0 then Z_p 0 (x1-y1^2) else Z_p 0 (x1-y1^2-y1)
			w = Z_p 1 $ Z_p y0 y1
		sq2 _ = error "admits no sqare root"
		sqp (Z_p 0 (Z_p 0 x)) = Z_p 0 $ sqp x
		sqp (Z_p b x) = Z_p a w where
			a = sqrtMod_p b 
			w =  invZ_p (2*a) * (x - Z_p (div_p (a^2-b)) (w^2))
	atan x = if p() `mod` 4 == 1 then la x else a x where
		la = \x -> log ((x-i)/(x+i)) / (2*i) where i = sqrt(-1)
		a x@(Z_p 0 _) = series x
		a x =  series (make x 1 0 1 0 0) / fromIntegral n
		series = inLogSeriesZ_p (cycle [1,0,-1,0::Digit]) . estimateOrderZ_p
		n = if p()==2 then 4 else p()+1 :: Integer
		make x s k t pp qq | k>n = pp/qq
			| odd k = make x (-s) (k+1) (t*x) (pp+y) qq
			| True = make x s (k+1) (t*x) pp (qq+y) where y = t*fromIntegral(s*choose n k)

-- p-1. Einheitswurzeln mit gegebener erster Ziffer a /= 0
rtUnityZ_p a' = Z_p a w where
	a = mod_p a'
	Z_p _ c = (1-fromIntegral (toInteger a^(p()-1))) / fromIntegral (toInteger a^(p()-2))
	(ai,p1i) = (invZ_p a, invZ_p (p()-1))
	wa = w * ai
	psum k wp = if k>p()-1 then 0 else Z_p 0 (psum (k+1) (wp*wa) ) + 
		fromIntegral (choose (p()-1) (toInteger k)) * wp
	w = p1i * (c - Z_p 0 (w*wa*psum 2 1))

-- Wendet Newtonverfahren auf einen Startwert a an. f(a) muß Ordnung mindestens 1 haben.
newtonZ_p f f' a = Z_p a' $ t 1 a where
	Z_p a' _ = a
	interval (a,b) = k 0 where
		k i (Z_p e r) z = if i<a then k (i+1) r z else if i<b then Z_p e $ k (i+1) r z else z
	t i x = interval (i,2*i) y $ t (2*i) y where
		y = x - f x / f' x

instance Show Z_p where
	show r = if p() > 31 then it else sch where
		maxIts = 5
		it = "[.." ++ tail(show $ reverse $ take maxIts $ f 1 0 r )
		f i acc (Z_p a r) = na : f (i*p()) na r where na = i*a+acc
		maxDigits = 20
		sch = w $ ps 0 r ""
		w "0" = "..0"
		w ('0':r) = w r
		w r = ".."++r
		sh i r = ((['0'..'9'] ++ ['a'..'z']) !! i) : r
		ps i (Z_p x r) a = if i > maxDigits then a else ps (i+1) r (sh x a)

-----------------------------------------------------------------------------------------

-- Q_p. o ist die Ordnung
-- Im Prinzip die Reimplementierung von Laurentreihen.
data Q_p = Q_p Int Z_p

-- Präzisions-Potenz. Braucht man zum Invertieren.
{-# NOINLINE q_pPrecRef #-}
q_pPrecRef = unsafePerformIO $ newIORef 60
q_pPrec = unsafePerformIO $ readIORef q_pPrecRef 

-- Bestimmt, ob eine Q_p Zahl kleiner als p^q_pPrec ist.
nearZeroQ_p (Q_p o z) = iter o z where
	iter o (Z_p 0 r) = if o > q_pPrec then True else iter (o+1) r
	iter o _ = False

-- Schneidet führende Nullen ab. Terminiert nach spätestens q_pPrec Schritten.
cleanQ_p (Q_p o r) = c o r where 
	c o (Z_p 0 r) = if o>q_pPrec then Q_p q_pPrec r else c (o+1) r
	c o r = Q_p o r

instance Num Q_p where
	Q_p o r + Q_p o' r' = if o<=o' then Q_p o (r + shiftZ_p (o'-o) r') else
			Q_p o' (shiftZ_p (o-o') r + r') 
	negate (Q_p o r) = Q_p o $ carry_p $ negate r
	fromInteger 0 = Q_p 0 0
	fromInteger i = Q_p o (fromInteger r) where (o,r)=orderRem_p i
	Q_p o r * Q_p o' r' = Q_p (o+o') (r*r')
	-- Q_p Norm
	abs (Q_p o r) = n (-o) r where
		n no (Z_p a r) = if no + q_pPrec < 0 then 0 else 
			if a==0 then n (no-1) r else Q_p no 1
	signum z = s (cleanQ_p z) where s (Q_p o r) = Q_p 0 $ signum r

instance Fractional Q_p where
	fromRational 0 = Q_p 0 0
	fromRational r = Q_p (oz-on) (fromRational (rz%rn)) where
		(z,n) = (numerator r, denominator r)
		(oz,rz) = orderRem_p z
		(on,rn) = orderRem_p n
	Q_p o r / qr = Q_p (o-o') (r/r') where Q_p o' r' = cleanQ_p qr

instance Eq Q_p where 
	z==zz = nearZeroQ_p $ z-zz

instance Ord Q_p where -- Das ist schon blöd
	compare a b = c (cleanQ_p a) (cleanQ_p b) where
		c (Q_p o _) (Q_p oo _) = compare oo o

instance Real Q_p where
	toRational (Q_p o z) = toRational z* if o>0 then p()^o else recip(p())^(-o)

-- Setzt eine Q_p-Zahl in eine exp-artige Reihe ein
inExpSeriesQ_p coeffs rx = if (p()-1)*o<=1 then error "series not convergent" else e where
	Q_p o r = cleanQ_p rx
	e = cleanQ_p $ Q_p 0 $ f 1 0 1 coeffs
	f n sh rp (c:co) = summand + shiftZ_p si (invZ_p rem *f (n+1)(sh+ds)(rp*r) co) where
		summand = shiftZ_p sh $ multZ_p c rp
		(z,rem) = orderRem_p n
		si = if n `mod` (p()-1) == 0 then o-1 else o
		ds = o-si-z

-- Setzt eine Q_p-Zahl in eine log-artige Reihe ein
inLogSeriesQ_p coeffs rx = if o<1 then error "series not convergent" else e where
	Q_p o r = cleanQ_p rx
	e = cleanQ_p $ Q_p o $ f 1 0 r coeffs
	f n sh rp (c:co) = summand + shiftZ_p si (f (n+1) (sh+o-si) (rp*r) co) where
		summand = shiftZ_p (sh-z) $ multZ_p c rp * invZ_p rem
		(z,rem) = orderRem_p n
		si = if rn == 1 then o-1 else o where (_,rn) = orderRem_p n

instance Floating Q_p where
	pi = 0
	exp = inExpSeriesQ_p $ repeat 1
	sin = inExpSeriesQ_p $ cycle [0,1,0,-1]
	cos = inExpSeriesQ_p $ cycle [1,0,-1,0]
	sinh =inExpSeriesQ_p $ cycle [0,1,0,1]
	cosh =inExpSeriesQ_p $ cycle [1,0,1,0]
	asinh x = log $ x + sqrt(x^2+1)
	acosh x = log $ x + sqrt(x^2-1)
	atanh x = log ((1+x)/(1-x)) / 2
	asin x = pi/2 - acos x
	acos x = atan (sqrt ((1-x)/(1+x)) )* 2
	sqrt (Q_p o r) = cleanQ_p $ Q_p h w where
		h = (o+1) `div` 2
		w = sqrt $ if odd o then Z_p 0 r else r
	log = l . cleanQ_p where
		l (Q_p _ r) = inLogSeriesQ_p (cycle [1,-1]) (Q_p 0 (r/signum r) - 1)
	atan x = if mod (p()-1) 4 == 0 then la x else if p()==2 then a2$cleanQ_p x else a$cleanQ_p x where
		la = \x -> log ((x-i)/(x+i)) / (2*i) where i = sqrt(-1)
		series = inLogSeriesQ_p (cycle [1,0,-1,0])
		a z@(Q_p o r)
			| o > 0 = series z
			| o < 0 = - series (recip z)
			| otherwise = series (make z 1 0 1 0 0) / (p()+1)
		a2 z = if nearZeroQ_p(1-z^2) then 0 else series(g$g z)/4 where g x = 2*x/(1-x^2)
		n = p()+1 :: Integer
		make x s k t pp qq | k>n = pp/qq
			| odd k = make x (-s) (k+1) (t*x) (pp+y) qq
			| True = make x s (k+1) (t*x) pp (qq+y) where y = t*fromIntegral(s*choose n k)

instance Show Q_p where
	show (Q_p o r) = if p() > 31 then it else sch where
		maxIts = 5
		it = "[.." ++ tail(show $ reverse $ take maxIts $ f (1%p()^o) 0 r )
		f i acc (Z_p a r) = na : f (i*p()) na r where na = i*fromIntegral a+acc
		maxDigits = 20
		sch = w $ ps o r $ if o>0 then replicate o '0' ++ "." else ""
		w "0" = "..0"
		w ('0':'.':r) = "..0."++r
		w ('0':r) = w r
		w r = ".."++r
		sh i r = ((['0'..'9'] ++ ['a'..'z']) !! i) : r
		ps i (Z_p x r) a = if i > maxDigits then a else ps (i+1) r (sh x $(if i==0 then "." else"")++a)
