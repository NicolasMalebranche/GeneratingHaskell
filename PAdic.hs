{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor #-}

-- Modul für p-adische Zahlen
module PAdic where

import PowerSeries
import Math.Combinatorics.Exact.Binomial
import System.IO.Unsafe
import Data.IORef
import Data.Ratio

-- Datentyp für Ziffern. Sollte p^2 noch enthalten
type Digit = Int

-- p, als globale Variable. Voreinstellung ist 2
{-# NOINLINE pRef #-}
pRef :: IORef Digit
pRef = unsafePerformIO $ newIORef 5
p = unsafePerformIO $ readIORef pRef

-----------------------------------------------------------------------------------------

-- Datentyp für Z_p über einer Zahl p
data Z_p = Z_p (PowerSeries Digit)

-- Übertrag 
carry_p = c 0 where
	c a (Elem i r) = Elem m $ c d r where (d,m) = divMod (a+i) p

-- Wandelt Potenzreihe in Z_p-Zahl um
makeZ_p r = Z_p $ carry_p r

-- Erweiterter Euklidischer Algorithmus
euclid 0 b = (b, (0, 1))
euclid a b = (gcd, (y - x*d, x)) where
	(d,m) = divMod b a
	(gcd, (x, y)) = euclid m a

-- Zählt p-Potenzen in einer Zahl
order_p i = if m==0 then 1+order_p d else 0 where 
	(d,m) = divMod i $ fromIntegral p

-- Inverses modulo p
invMod_p n = if gcd == 1 then mod x p else error $"division by "++show n++" mod "++show p where
	(gcd,(x,_)) = euclid nn p
	nn = fromIntegral $ mod n $ fromIntegral p

-- Inverses einer Zahl in Z_p, aber als Potenzreihe
invZ_p :: Digit -> PowerSeries Digit
invZ_p a = d 1 where
	a' = invMod_p a
	d c = Elem t $ d $ div (c-a*t) p where t = mod (c*a') p

-- Wurzel modulo p, einfach durch Ausprobieren
sqrtMod_p n = f 0 where
	f i = if mod(i^2 - n) p == 0 then i else if i<p then f (i+1) else
		error $ show n++" admits no sqrt mod "++show p

instance Num Z_p where
	fromInteger i = Z_p $ c i where
		c i = Elem (fromInteger m) $ c d  where (d,m) = divMod i $ fromIntegral p
	Z_p x + Z_p y = makeZ_p $ x+y
	Z_p x - Z_p y = makeZ_p $ x-y
	Z_p x * Z_p y = makeZ_p $ x*y
	signum (Z_p (Elem a r)) = Z_p $ Elem a $ nullSeries ()
	abs = id

instance Fractional Z_p where
	Z_p (Elem c rC) / Z_p (Elem a rA) = Z_p bb where
		a' = invMod_p a
		d c = Elem t $ d $ div (c-a*t) p where t = mod (c*a') p
		b = mod (c*a') p
		r = Elem (div (c-a*b) p) 0
		bb = Elem b $ carry_p $ d 1 * (r + rC - rA*bb)
	fromRational r = Z_p $ d $ numerator r where
		a = denominator r
		a' = fromIntegral $ invMod_p a
		pp = fromIntegral p
		d c = Elem (fromIntegral b) $ d $ div (c-a*b) pp where 
			b = mod (c*a') pp

-- Quadratwurzel
sqrtZ_p (Z_p x) = Z_p $ if p==2 then sq2 x else sqp x where
	sq2 (Elem 0 (Elem 0 x)) = Elem 0 $ sq2 x
	sq2 (Elem 1 (Elem 0 (Elem 0 (Elem x0 x1)))) = w where
		y0 = if odd x0 then 1 else 0
		y1 = carry_p $ if y0 == 0 then Elem 0 (x1-y1^2) else Elem 0 (x1-y1^2-y1)
		w = Elem 1 $ Elem y0 y1
	sq2 _ = error "admits no sqare root"
	sqp (Elem 0 (Elem 0 x)) = Elem 0 $ sqp x
	sqp (Elem b x) = Elem a w where
		a = sqrtMod_p b 
		w = carry_p $ invZ_p (2*a) * (x - Elem (div (a^2-b) p) (w^2))

-- p-1. Einheitswurzeln mit gegebener erster Ziffer a /= 0
rtUnityZ_p a' = Z_p $ Elem a w where
	a = a' `mod` p
	Z_p c = (1-fromIntegral a^(p-1)) / fromIntegral a^(p-2)
	(ai,p1i) = (invZ_p a, invZ_p (p-1))
	wa = carry_p $ w * ai
	psum k wp = if k>p-1 then 0 else Elem 0 (psum (k+1) (carry_p(wp*wa)) ) + 
		fmap (* choose(p-1)k) wp
	w = carry_p $ p1i*(seriesShift (-1) c - Elem 0 (carry_p(w*wa)*psum 2 1))

instance Show Z_p where
	show (Z_p r) = if p > 10 then it else sch where
		maxIts = 5
		it = "[.." ++ tail(show $ reverse $ take maxIts $ f 1 0 r )
		f i acc (Elem a r) = na : f (i*p) na r where na = i*a+acc
		maxDigits = 20
		sch = w $ ps 0 r ""
		w "0" = "..0"
		w ('0':r) = w r
		w r = ".."++r
		ps i (Elem x r) a = if i > maxDigits then a else ps (i+1) r (show x ++a)

-----------------------------------------------------------------------------------------

-- Q_p. o ist die Ordnung
-- Im Prinzip die Reimplementierung von Laurentreihen.
data Q_p = Q_p Int (PowerSeries Digit) 

-- Präzisions-Potenz für Laurentreihen. Braucht man zum Invertieren.
{-# NOINLINE q_pPrecRef #-}
q_pPrecRef = unsafePerformIO $ newIORef 60
q_pPrec = unsafePerformIO $ readIORef q_pPrecRef 

-- Wandelt Potenzreihe in Q_p-Zahl um
makeQ_p r = Q_p 0 $ c 0 r where
	c a (Elem i r) = Elem m $ c d r where (d,m) = divMod (a+i) p

-- Schneidet führende Nullen ab
cleanQ_p (Q_p o p) = c o p where 
	c o (Elem 0 p) = if o>q_pPrec then Q_p q_pPrec p else c (o+1) p
	c o p = Q_p o p

instance Num Q_p where
	Q_p o r + Q_p o' r' = if o<=o' then Q_p o $carry_p (r + seriesShift (o'-o) r') else
			Q_p o' $ carry_p (seriesShift (o-o') r + r') 
	negate (Q_p o r) = Q_p o $ carry_p $ negate r
	fromInteger 0 = Q_p 0 0
	fromInteger i = f 0 i where
		f o i = if m==0 then f (o+1) d else Q_p o (c i) where (d,m)=divMod i $ fromIntegral p
		c i = Elem (fromInteger m) $ c d  where (d,m) = divMod i $ fromIntegral p
	Q_p o r * Q_p o' r' = Q_p (o+o') $ carry_p $ r*r'
	-- Q_p Norm
	abs (Q_p o r) = n (-o) r where
		n no (Elem a r) = if no + q_pPrec < 0 then 0 else 
			if a==0 then n (no-1) r else Q_p no 1
	signum = id

instance Fractional Q_p where
	fromRational 0 = Q_p 0 0
	fromRational r = Q_p o q where
		(z,n,pp) = (numerator r, denominator r,fromIntegral p)
		dd i = if m==0 then dd d else i where (d,m) = divMod i pp
		o = order_p z - order_p n
		Z_p q = fromRational (dd z % dd n)
	Q_p o r / qr = Q_p (o-o') q where
		Q_p o' r' = cleanQ_p qr
		Z_p q = Z_p r/Z_p r'

-- Setzt eine Q_p-Zahl in eine exp-artige Reihe ein
inExpSeriesQ_p coeffs rx = if (p-1)*o<=1 then error "series not convergent" else makeQ_p e where
	Q_p o r = cleanQ_p rx
	e = f 1 0 1 coeffs
	f n sh rp (c:co) = carry_p value where
		value = summand + seriesShift si (fakt * f (n+1) (sh+ds) (carry_p (rp*r)) co)
		summand = seriesShift sh $ fmap (c*) rp
		z = order_p n
		si = if n `mod` (p-1) == 0 then o-1 else o
		fakt = invZ_p (n `div` (p^z))
		ds = o-si-z

instance Floating Q_p where
	exp = inExpSeriesQ_p $ repeat 1
	sin = inExpSeriesQ_p $ cycle [0,1,0,-1]
	cos = inExpSeriesQ_p $ cycle [1,0,-1,0]
	sinh =inExpSeriesQ_p $ cycle [0,1,0,1]
	cosh =inExpSeriesQ_p $ cycle [1,0,1,0]
	sqrt (Q_p o r) = cleanQ_p $ Q_p h w where
		h = (o+1) `div` 2
		Z_p w = sqrtZ_p $ Z_p $ if odd o then Elem 0 r else r

instance Show Q_p where
	show (Q_p o r) = if p > 10 then it else sch where
		maxIts = 5
		it = "[.." ++ tail(show $ reverse $ take maxIts $ f (1%p^o) 0 r )
		f i acc (Elem a r) = na : f (i*fromIntegral p) na r where na = i*fromIntegral a+acc
		maxDigits = 20
		sch = w $ ps o r $ if o>0 then replicate o '0' ++ "." else ""
		w "0" = "..0"
		w ('0':'.':r) = "..0."++r
		w ('0':r) = w r
		w r = ".."++r
		ps i (Elem x r) a = if i > maxDigits then a else ps (i+1) r (show x ++(if i==0 then "." else"")++a)
