{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor #-}

-- Modul für p-adische Zahlen
module PAdic where

import PowerSeries
import System.IO.Unsafe
import Data.IORef
import Data.List.Utils
import Data.Ratio

-- Datentyp für Ziffern. Sollte p^2 noch enthalten
type Digit = Int

-- p, als globale Variable. Voreinstellung ist 2
pRef :: IORef Digit
pRef = unsafePerformIO $ newIORef 2
p = unsafePerformIO $ readIORef pRef

-----------------------------------------------------------------------------------------

-- Datentyp für Z_p über einer Zahl p
data Z_p = Z_p (PowerSeries Digit)

-- Wandelt Potenzreihe in Z_p-Zahl um
makeZ_p r = Z_p $ c 0 r where
	c a (Elem i r) = Elem m $ c d r where (d,m) = divMod (a+i) p

-- Erweiterter Euklidischer Algorithmus
euclid 0 b = (b, (0, 1))
euclid a b = (gcd, (y - x*d, x)) where
	(d,m) = divMod b a
	(gcd, (x, y)) = euclid m a

-- Inverses modulo p
invMod_p n = if gcd == 1 then mod x p else error $"division by "++show n++" mod "++show p where
	(gcd,(x,_)) = euclid n p

instance Num Z_p where
	fromInteger i = Z_p $ fmap fromInteger $ c i $ nullSeries () where
		c a (Elem i r) = Elem m $ c d r where (d,m) = divMod (a+i) $ fromIntegral p
	Z_p x + Z_p y = makeZ_p $ x+y
	Z_p x - Z_p y = makeZ_p $ x-y
	Z_p x * Z_p y = makeZ_p $ x*y
	signum (Z_p (Elem a r)) = Z_p $ Elem a $ nullSeries ()
	abs = id

instance Fractional Z_p where
	Z_p (Elem ga c) / Z_p (Elem al a) = makeZ_p bb where
		alin = invMod_p al
		bb = Elem (ga*alin) $ fmap (*alin) $ c-a*bb
	fromRational r = fromIntegral (numerator r) / fromIntegral (denominator r)

instance Show Z_p where
	show (Z_p r) = if p > 10 then replace "x" "p" (show r) else sch where
		maxDigits = 20
		sch = w $ ps 0 r ""
		w "0" = "..0"
		w ('0':r) = w r
		w r = ".."++r
		ps i (Elem x r) a = if i > maxDigits then a else ps (i+1) r (show x ++a)

-----------------------------------------------------------------------------------------

