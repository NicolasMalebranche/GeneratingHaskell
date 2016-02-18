{-# LANGUAGE TypeFamilies, EmptyDataDecls, FlexibleContexts, 
			  UndecidableInstances  #-}
module F_p where

import Data.Ratio
import Data.Int
import PrimeFactors

-- Stellt ein paar Mod-p Koerper zur Verfuegung
-- Hat man Bedarf fuer einen neuen, kann man wie bei 
-- den folgenden Beispielen vorgehen.
-- Die Instanzen von Eq, Num, Fractional, Show werden dann
-- automatisch erzeugt

data Mod2
newtype instance F Mod2 = Mod2 Int8
instance ModP Mod2 where
	type ModStore Mod2 = Int8
	p _ = 2
	con = Mod2
	decon (Mod2 i) = i

data Mod3
newtype instance F Mod3 = Mod3 Int8
instance ModP Mod3 where
	type ModStore Mod3 = Int8
	p _ = 3
	con = Mod3
	decon (Mod3 i) = i

data Mod5
newtype instance F Mod5 = Mod5 Int8
instance ModP Mod5 where
	type ModStore Mod5 = Int8
	p _ = 5
	con = Mod5
	decon (Mod5 i) = i

data Mod7
newtype instance F Mod7 = Mod7 Int8
instance ModP Mod7 where
	type ModStore Mod7 = Int8
	p _ = 7
	con = Mod7
	decon (Mod7 i) = i

-- Fuer p > 2^14 sollte man seine Zahlen nicht
-- mehr als Int speichern, sondern z. B. als Integer
data Mod23879539
newtype instance F Mod23879539 = Mod23879539 Integer
instance ModP Mod23879539 where
	type ModStore Mod23879539 = Integer
	p _ = 23879539
	con = Mod23879539
	decon (Mod23879539 i) = i


-- Und hier die Trickserei dahinter:

data family F :: * -> *

class (Integral (ModStore a)) => ModP a where
	type ModStore a :: *
	p :: F a -> ModStore a
	con :: ModStore a -> F a
	decon :: F a -> ModStore a
	

class (Fractional f) => FiniteField f where
	primRoot :: f
	ffChar :: Integral i => f -> i
	ffOrder :: Integral i => f -> i
	ffAll :: [f]

instance (ModP fp) => FiniteField (F fp) where
	primRoot = r where 
		r = check 1 
		phi =  fromIntegral (p r) - 1 
		divs = map (div phi . fst) (primeFactors phi) 
		check r = if all (/=1) [ r^e | e<-divs ] 
			then r else check (r+1)
	ffChar = fromIntegral . p
	ffOrder = fromIntegral . p
	ffAll = [0..]
	

instance (ModP fp ,Show (ModStore fp)) => Show (F fp) where
	show x = show (decon x) -- ++ " (mod " ++ show (p x) ++ ")"

instance (ModP fp) => Eq (F fp) where
	a == b = 0 == ((decon a - decon b) `mod` (p a))

instance (ModP fp) => Ord (F fp) where
	compare a b = compare (decon a)  (decon b)

instance (ModP fp) => Num (F fp) where
	a + b = con $ (decon a + decon b) `mod` (p a)
	a - b = con $ (decon a - decon b) `mod` (p a)
	a * b = con $ (decon a * decon b) `mod` (p a)
	abs = undefined
	signum = undefined
	fromInteger i = x where 
		x = con $ fromInteger $ i `mod` fromIntegral (p x)

instance (ModP fp) => Fractional (F fp) where
	recip a = con $ ra where
		(_,(ra,_)) = euclid (decon a) (p a)
		euclid 0 b = (b, (0, 1))
		euclid a b = (gcd, (y - x*d, x)) where
			(d,m) = divMod b a
			(gcd, (x, y)) = euclid m a
	fromRational r = fromInteger (numerator r) / 
		fromInteger (denominator r)

instance (ModP fp) => Enum (F fp) where
	toEnum i = x where x = con $ fromIntegral i `mod` p x
	fromEnum = fromIntegral . decon
	succ x = x+1
	pred x = x-1
	enumFromTo a b = if a==b then [a] else a : enumFromTo (a+1) b
	enumFrom a = enumFromTo a (a-1)
	enumFromThenTo a s b = if a == b then [a] else a : enumFromThenTo s (s*2-a) b
	enumFromThen a s = enumFromThenTo a s (a*2-s)


