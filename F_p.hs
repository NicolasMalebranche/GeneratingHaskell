{-# LANGUAGE TypeFamilies, EmptyDataDecls, FunctionalDependencies, 
			 MultiParamTypeClasses, UndecidableInstances  #-}
module F_p where

import Data.Ratio

-- Stellt ein paar Mod-p Koerper zur Verfuegung
-- Hat man Bedarf fuer einen neuen, kann man wie bei 
-- den folgenden Beispielen vorgehen.
-- Die Instanzen von Eq, Num, Fractional, Show werden dann
-- automatisch erzeugt

data Mod2
newtype instance F Mod2 = Mod2 Int
instance ModP Mod2 Int where
	p _ = 2
	con = Mod2
	decon (Mod2 i) = i
	primRoot = 1

data Mod3
newtype instance F Mod3 = Mod3 Int
instance ModP Mod3 Int where
	p _ = 3
	con = Mod3
	decon (Mod3 i) = i
	primRoot = 2

data Mod5
newtype instance F Mod5 = Mod5 Int
instance ModP Mod5 Int where
	p _ = 5
	con = Mod5
	decon (Mod5 i) = i
	primRoot = 2

data Mod7
newtype instance F Mod7 = Mod7 Int
instance ModP Mod7 Int where
	p _ = 7
	con = Mod7
	decon (Mod7 i) = i
	primRoot = 3

-- Fuer p > 2^16 sollte man seine Zahlen nicht
-- mehr als Int speichern, sondern z. B. als Integer
data Mod23879539
newtype instance F Mod23879539 = Mod23879539 Integer
instance ModP Mod23879539 Integer where
	p _ = 23879539
	con = Mod23879539
	decon (Mod23879539 i) = i


-- Und hier die Trickserei dahinter:

data family F :: * -> *

class Integral i => ModP a i | a->i where
	p :: F a -> i
	con :: i -> F a
	decon :: F a -> i
	primRoot :: F a

instance (ModP fp i, Show i) => Show (F fp) where
	show x = show (decon x) -- ++ " (mod " ++ show (p x) ++ ")"

instance (ModP fp i) => Eq (F fp) where
	a == b = 0 == ((decon a - decon b) `mod` (p a))

instance (ModP fp i) => Num (F fp) where
	a + b = con $ (decon a + decon b) `mod` (p a)
	a - b = con $ (decon a - decon b) `mod` (p a)
	a * b = con $ (decon a * decon b) `mod` (p a)
	abs = undefined
	signum = undefined
	fromInteger i = x where 
		x = con $ fromInteger $ i `mod` fromIntegral (p x)

instance (ModP fp i) => Fractional (F fp) where
	recip a = con $ ra where
		(_,(ra,_)) = euclid (decon a) (p a)
		euclid 0 b = (b, (0, 1))
		euclid a b = (gcd, (y - x*d, x)) where
			(d,m) = divMod b a
			(gcd, (x, y)) = euclid m a
	fromRational r = fromInteger (numerator r) / 
		fromInteger (denominator r)

instance (ModP fp i) => Enum (F fp) where
	toEnum i = x where x = con $ fromIntegral i `mod` p x
	fromEnum = fromIntegral . decon
	succ x = x+1
	pred x = x-1
	enumFromTo a b = if a==b then [a] else a : enumFromTo (a+1) b
	enumFrom a = enumFromTo a (a-1)
	enumFromThenTo a s b = if a == b then [a] else a : enumFromThenTo s (s*2-a) b
	enumFromThen a s = enumFromThenTo a s (a*2-s)



