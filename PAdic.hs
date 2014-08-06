{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor #-}

-- Modul für p-adische Zahlen
module PAdic where

import PowerSeries
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

-----------------------------------------------------------------------------------------

-- Datentyp für Z_p über einer Zahl p
data Z_p = Z_p (PowerSeries Digit)

-- Übertrag 
carry_p r = c 0 r where
	c a (Elem i r) = Elem m $ c d r where (d,m) = divMod (a+i) p

-- Wandelt Potenzreihe in Z_p-Zahl um
makeZ_p r = Z_p $ carry_p r

-- Erweiterter Euklidischer Algorithmus
euclid 0 b = (b, (0, 1))
euclid a b = (gcd, (y - x*d, x)) where
	(d,m) = divMod b a
	(gcd, (x, y)) = euclid m a

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
