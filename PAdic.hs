{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor #-}

-- Modul für p-adische Zahlen
module PAdic where

import Math.Combinatorics.Exact.Binomial
import System.IO.Unsafe
import Data.IORef
import Data.Ratio

-- Datentyp für Ziffern. Sollte p^2 noch enthalten
type Digit = Int

-- p, als globale Variable. Voreinstellung ist 2
{-# NOINLINE pRef #-}
pRef :: IORef Digit
pRef = unsafePerformIO $ newIORef 2
p = unsafePerformIO $ readIORef pRef
pp _ = fromIntegral p

-----------------------------------------------------------------------------------------

-- Datentyp für Z_p über einer Zahl p
data Z_p = Z_p Digit Z_p

-- Übertrag 
carry_p = c 0 where c a (Z_p i r) = Z_p m $ c d r where (d,m) = divMod (a+i) p

-- Erweiterter Euklidischer Algorithmus
euclid 0 b = (b, (0, 1))
euclid a b = (gcd, (y - x*d, x)) where
	(d,m) = divMod b a
	(gcd, (x, y)) = euclid m a

-- Zählt p-Potenzen in einer Zahl
-- Achtung! Terminiert nicht, wenn 0 eingegeben wird
order_p i = if m==0 then 1+order_p d else 0 where 
	(d,m) = divMod i $ pp()

-- orderRem_p n = (o,r) wobei n==(p^o)*r und o maximal
-- Achtung! Terminiert nicht, wenn 0 eingegeben wird
orderRem_p :: (Integral i,Integral j) => i -> (j,i)
orderRem_p = c 0 where 
	c o n = if m==0 then c (o+1) d else (o,n) where (d,m) = divMod n $ pp()

-- Inverses modulo p
invMod_p n = if gcd == 1 then mod x p else error $"division by "++show n++" mod "++show p where
	(gcd,(x,_)) = euclid nn p
	nn = fromIntegral $ mod n $ pp ()

-- Wurzel modulo p, einfach durch Ausprobieren
sqrtMod_p n = f 0 where
	f i = if mod(i^2 - n) p == 0 then i else if i<p then f (i+1) else
		error $ show n++" admits no sqrt mod "++show p

-- Multipliziert mit p^k in Z_p. Schneidet Ziffern ab, falls k < 0
shiftZ_p k = if k < 0 then left k else right k where
	right k z = if k==0 then z else Z_p 0 $ right (k-1) z
	left k (Z_p _ r) = if k== -1 then r else left (k+1) r

-- Multipliziert eine Z_p Zahl mit einem Skalar s
multZ_p s = c 0 where c u (Z_p a r) = Z_p m $ c d r where (d,m) = divMod (s*a+u) p

-- Inverses einer ganzen Zahl in Z_p
invZ_p a = d 1 where
	a' = invMod_p a
	d c = Z_p t $ d $ div (c-a*t) p where t = mod (c*a') p

instance Num Z_p where
	fromInteger i = Z_p (fromInteger m) $ fromInteger d  where (d,m)= divMod i $ pp ()
	(+) = c 0 where c u (Z_p a x)(Z_p b y) = Z_p m $c d x y where (d,m)= divMod (u+a+b) p
	(-) = c 0 where c u (Z_p a x)(Z_p b y) = Z_p m $c d x y where (d,m)= divMod (u+a-b) p
	signum (Z_p a r) = if a==0 then 0 else rtUnityZ_p a
	abs (Z_p a _) = if a==0 then undefined else 1
	-- Achtung! Es wird nur einmal Übertrag gemacht.
	(*) (Z_p afst arst) = carry_p . f facc arst where
		f acc ale br = Z_p (acc br) $ f newacc ar br where
			Z_p a ar = ale
			newacc (Z_p b rb) = a*b + acc rb
		facc (Z_p b rb) = afst*b

instance Fractional Z_p where
	Z_p c rC / Z_p a rA = bb where
		a' = invMod_p a
		d c = Z_p t $ d $ div (c-a*t) p where t = mod (c*a') p
		b = mod (c*a') p
		r = Z_p (div (c-a*b) p) 0
		bb = Z_p b $ d 1 * (r + rC - rA*bb)
	fromRational r = d $ numerator r where
		a = denominator r
		a' = fromIntegral $ invMod_p a
		d c = Z_p (fromIntegral b) $ d $ div (c-a*b) $ pp() where 
			b = mod (c*a') $ pp()

-- Quadratwurzel
sqrtZ_p x= if p==2 then sq2 x else sqp x where
	sq2 (Z_p 0 (Z_p 0 x)) = Z_p 0 $ sq2 x
	sq2 (Z_p 1 (Z_p 0 (Z_p 0 (Z_p x0 x1)))) = w where
		y0 = if odd x0 then 1 else 0
		y1 = if y0 == 0 then Z_p 0 (x1-y1^2) else Z_p 0 (x1-y1^2-y1)
		w = Z_p 1 $ Z_p y0 y1
	sq2 _ = error "admits no sqare root"
	sqp (Z_p 0 (Z_p 0 x)) = Z_p 0 $ sqp x
	sqp (Z_p b x) = Z_p a w where
		a = sqrtMod_p b 
		w =  invZ_p (2*a) * (x - Z_p (div (a^2-b) p) (w^2))

-- p-1. Einheitswurzeln mit gegebener erster Ziffer a /= 0
rtUnityZ_p a' = Z_p a w where
	a = a' `mod` p
	Z_p _ c = (1-fromIntegral (toInteger a^(p-1))) / fromIntegral (toInteger a^(p-2))
	(ai,p1i) = (invZ_p a, invZ_p (p-1))
	wa = w * ai
	psum k wp = if k>p-1 then 0 else Z_p 0 (psum (k+1) (wp*wa) ) + 
		fromIntegral (choose (pp()-1) (toInteger k)) * wp
	w = p1i * (c - Z_p 0 (w*wa*psum 2 1))

-- Wendet Newtonverfahren auf einen Startwert a an. f(a) muß Ordnung mindestens 1 haben.
newtonZ_p f f' a = Z_p a' $ t 1 a where
	Z_p a' _ = a
	interval (a,b) = k 0 where
		k i (Z_p e r) z = if i<a then k (i+1) r z else if i<b then Z_p e $ k (i+1) r z else z
	t i x = interval (i,2*i) y $ t (2*i) y where
		y = x - f x / f' x

instance Show Z_p where
	show r = if p > 10 then it else sch where
		maxIts = 5
		it = "[.." ++ tail(show $ reverse $ take maxIts $ f 1 0 r )
		f i acc (Z_p a r) = na : f (i*p) na r where na = i*a+acc
		maxDigits = 20
		sch = w $ ps 0 r ""
		w "0" = "..0"
		w ('0':r) = w r
		w r = ".."++r
		ps i (Z_p x r) a = if i > maxDigits then a else ps (i+1) r (show x ++a)

-----------------------------------------------------------------------------------------

-- Q_p. o ist die Ordnung
-- Im Prinzip die Reimplementierung von Laurentreihen.
data Q_p = Q_p Int Z_p

-- Präzisions-Potenz für Laurentreihen. Braucht man zum Invertieren.
{-# NOINLINE q_pPrecRef #-}
q_pPrecRef = unsafePerformIO $ newIORef 60
q_pPrec = unsafePerformIO $ readIORef q_pPrecRef 

-- Schneidet führende Nullen ab. Terminiert nach spätestens q_pPrec Schritten.
cleanQ_p (Q_p o p) = c o p where 
	c o (Z_p 0 p) = if o>q_pPrec then Q_p q_pPrec p else c (o+1) p
	c o p = Q_p o p

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

-- Setzt eine Q_p-Zahl in eine exp-artige Reihe ein
inExpSeriesQ_p coeffs rx = if (p-1)*o<=1 then error "series not convergent" else e where
	Q_p o r = cleanQ_p rx
	e = cleanQ_p $ Q_p 0 $ f 1 0 1 coeffs
	f n sh rp (c:co) = summand + shiftZ_p si (invZ_p rem *f (n+1)(sh+ds)(rp*r) co) where
		summand = shiftZ_p sh $ multZ_p c rp
		(z,rem) = orderRem_p n
		si = if n `mod` (p-1) == 0 then o-1 else o
		ds = o-si-z

-- Setzt eine Q_p-Zahl in eine log-artige Reihe ein
inLogSeriesQ_p coeffs rx = if o<1 then error "series not convergent" else e where
	Q_p o r = cleanQ_p rx
	e = cleanQ_p $ Q_p o $ f 1 0 r coeffs
	f n sh rp (c:co) = summand + shiftZ_p si (f (n+1) (sh+o-si) (rp*r) co) where
		summand = shiftZ_p (sh-z) $ multZ_p c rp * invZ_p rem
		(z,rem) = orderRem_p n
		si = if rn == 1 then o-1 else o where (_,rn) = orderRem_p n

-- Setzt p mal eine Z_p-Zahl in eine log-artige Reihe ein
inLogSeriesZ_p coeffs r = f 1 1 r coeffs where
	f n sh rp (c:co) = summand + shiftZ_p si (f (n+1) (sh+1-si) (rp*r) co) where
		summand = shiftZ_p (sh-z) $ multZ_p c rp * invZ_p rem
		(z,rem) = orderRem_p n
		si = if rn == 1 then 0 else 1 where (_,rn) = orderRem_p n

instance Floating Q_p where
	exp = inExpSeriesQ_p $ repeat 1
	sin = inExpSeriesQ_p $ cycle [0,1,0,-1]
	cos = inExpSeriesQ_p $ cycle [1,0,-1,0]
	sinh =inExpSeriesQ_p $ cycle [0,1,0,1]
	cosh =inExpSeriesQ_p $ cycle [1,0,1,0]
	sqrt (Q_p o r) = cleanQ_p $ Q_p h w where
		h = (o+1) `div` 2
		w = sqrtZ_p $ if odd o then Z_p 0 r else r
	log = Q_p 1 . l . cleanQ_p where
		l (Q_p _ r) = logser 1 z where
			Z_p _ z = r / signum r
			logser i acc = shiftZ_p(i-1-o1)(acc*invZ_p r1) + 
				shiftZ_p(i-o2)(zacc*invZ_p r2) +Z_p 0 (logser (i+1) (z*zacc)) where 
					zacc = z*acc
					(o1,r1) = orderRem_p (2*i-1)
					(o2,r2) = orderRem_p (-2*i)
	atan = a.cleanQ_p where
		a z@(Q_p o r) = if o == 0 then (inLogSeriesQ_p (cycle [1,0,-1,0]) $ f$ f z)/4 else
			(inLogSeriesQ_p (cycle [1,0,-1,0]) $ f z)/2
		f z = 2*z / (1-z^2)

instance Show Q_p where
	show (Q_p o r) = if p > 10 then it else sch where
		maxIts = 5
		it = "[.." ++ tail(show $ reverse $ take maxIts $ f (1%p^o) 0 r )
		f i acc (Z_p a r) = na : f (i*fromIntegral p) na r where na = i*fromIntegral a+acc
		maxDigits = 20
		sch = w $ ps o r $ if o>0 then replicate o '0' ++ "." else ""
		w "0" = "..0"
		w ('0':'.':r) = "..0."++r
		w ('0':r) = w r
		w r = ".."++r
		ps i (Z_p x r) a = if i > maxDigits then a else ps (i+1) r (show x ++(if i==0 then "." else"")++a)
