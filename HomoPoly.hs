{-# OPTIONS -fglasgow-exts  -XUndecidableInstances #-}
module HomoPoly where

import Data.List

-- Experimentelles Modul, um homogene Polynome zu modellieren

data Zero
data Succ n
type One = Succ Zero
type Two = Succ One

class Add a b ab | a b -> ab , a ab -> b
instance Add Zero b b
instance (Add a b ab) => Add (Succ a) b (Succ ab)

add :: (Add a b ab) => a -> b -> ab 
add _ _ = undefined
sub :: (Add a b ab) => ab -> a -> b
sub _ _ = undefined  

class Nat n where natToInt :: n -> Int

instance          Nat Zero     where natToInt _ = 0
instance Nat n => Nat (Succ n) where natToInt _ = 1 + natToInt (undefined::n)

class Nat n => Nat1 n  -- Klasse fuer Zahlen groessergleich 1
instance Nat n => Nat1 (Succ n)
class Nat1 n => Nat2 n -- Klasse fuer Zahlen groessergleich 2
instance Nat1 n => Nat2 (Succ n)


data HomoPoly a v d where
	Coeff :: (Num a, Nat v) => a -> HomoPoly a v Zero
	Monom :: (Num a, Nat1 d) => a -> HomoPoly a One d
	HSum  :: (Nat1 v, Nat d) => HomoPoly a (Succ v) d 		 -> 
								HomoPoly a v		(Succ d) -> 
								HomoPoly a (Succ v) (Succ d) 

-- Beispiele
bsp1 = HSum (Coeff 1) (Monom 1) -- x+y
bsp2 = HSum bsp1 (Monom 1) -- x²+xy+z²
bsp3 = HSum (Coeff 1) bsp1  -- w+x+y
bsp4 = HSum bsp3 $ HSum bsp1 $ Monom 1 -- w²+x²+y²+wx+wy+xy

class HP p where 
	pvar :: p -> Int
	pdeg :: p -> Int

instance (Nat v, Nat d) => HP (HomoPoly a v d) where
	pvar _ = natToInt (undefined :: v)
	pdeg _ = natToInt (undefined :: d)


instance (Eq a,Nat v) => Eq (HomoPoly a v Zero) where
	Coeff a == Coeff b = a==b
instance (Eq a,Nat d) => Eq (HomoPoly a One (Succ d)) where
	Monom a == Monom b = a==b
instance (Eq a, Nat v, Nat d, Eq (HomoPoly a (Succ v) (Succ d)), Eq (HomoPoly a (Succ (Succ v)) d)) =>
	Eq (HomoPoly a (Succ (Succ v)) (Succ d)) where
	HSum x y == HSum l r = x==l && y==r

instance (Num a,Nat v) => Num (HomoPoly a v Zero) where
	fromInteger i = Coeff $ fromInteger i
	negate (Coeff a) = Coeff (negate a)
	(+) (Coeff a) (Coeff b) = Coeff (a+b)
	(*) (Coeff a) (Coeff b) = Coeff (a*b)
	abs (Coeff a) = Coeff (abs a)
	signum (Coeff a) = Coeff (signum a)

instance (Num a,Nat d) => Num (HomoPoly a One (Succ d)) where
	fromInteger i = Monom 0
	negate (Monom a ) = Monom $ negate a
	(+) (Monom a) (Monom b) = Monom (a+b)
	abs = undefined
	signum = undefined
	(*) = undefined

instance (Num a, Nat v, Nat d, Num (HomoPoly a (Succ v) (Succ d)), Num (HomoPoly a (Succ (Succ v)) d)) =>
	Num (HomoPoly a (Succ (Succ v)) (Succ d)) where
		fromInteger i = HSum (fromInteger i) (fromInteger i)
		negate (HSum l r) = HSum (negate l) (negate r)
		HSum x y + HSum l r = HSum (x+l) (y+r)
		abs = undefined
		signum = undefined
		(*) = undefined

instance Show a => Show (HomoPoly a v d) where
	show p = concat $ intersperse "+" $ map reverse $ mono p
mono :: (Show a) => HomoPoly a v d -> [[Char]]
mono (Coeff a) = [reverse $ show a]
mono m@(Monom a) = [reverse $ show a ++ replicate (pdeg m) 'y']
mono (HSum l r) = map ((:) (['z','y'..]!!pvar l)) (mono l) ++ mono r

-- Zum Multiplizieren
scalar :: Num a => a -> HomoPoly a v d -> HomoPoly a v d
scalar a (Coeff b) = Coeff $ a*b
scalar a (Monom b) = Monom $ a*b
scalar a (HSum l r) = HSum (scalar a l) (scalar a r)

addVariable :: (Num a, Nat v, Nat d, Num (HomoPoly a (Succ v) d )) 
	=> HomoPoly a v (Succ d) -> HomoPoly a (Succ v) (Succ d) 
addVariable m@(Monom _) = HSum 0 m
addVariable s@(HSum _ _) = HSum 0 s

class GradedMult a v d dd ddd | d dd -> ddd where 
	gmult :: HomoPoly a v d -> HomoPoly a v dd -> HomoPoly a v ddd

class (Nat v, Nat d, Nat dd, Nat ddd) => 
	GradedMultHelper a v d dd ddd | d dd -> ddd where
		gmh :: HomoPoly a v d -> HomoPoly a (Succ v) dd -> HomoPoly a (Succ v) ddd

instance (Num a, Nat v, Nat d) => GradedMultHelper a v Zero d d where
	gmh (Coeff s) = scalar s

instance (Num a, Nat d, Num (HomoPoly a Two d)) 
	=> GradedMultHelper a One (Succ d) Zero (Succ d) where
	gmh (Monom a) (Coeff s) =  HSum 0 (Monom $ a*s)
instance (Num a, GradedMultHelper a One (Succ d) dd ddd) 
	=> GradedMultHelper a One (Succ d) (Succ dd) (Succ ddd) where
	gmh m@(Monom a) (HSum l (Monom b)) = HSum (gmh m l) (Monom $ a*b)

instance (Nat v, Num a, Nat d, Num (HomoPoly a (Succ (Succ (Succ v))) d)) 
	=>  GradedMultHelper a (Succ (Succ v)) (Succ d) Zero (Succ d) where
	gmh p (Coeff s) = HSum 0 $ scalar s p
instance (Nat v, GradedMultHelper a (Succ (Succ v)) d dd ddd, 
	GradedMult a (Succ (Succ v)) d (Succ dd) (Succ ddd)) 
	=> GradedMultHelper a (Succ (Succ v)) d (Succ dd) (Succ ddd) where
	gmh p (HSum l r) = HSum (gmh p l) (gmult p r)


instance (Num a, Nat v, Nat d) => GradedMult a v Zero d d where
	gmult (Coeff s) = scalar s

instance (Num a, Nat d) => GradedMult a One (Succ d) Zero (Succ d) where
	gmult (Monom a) (Coeff s) = Monom $ a*s
instance (Num a, Nat d, Nat ddd, GradedMult a One (Succ d) dd ddd ) 
	=> GradedMult a One (Succ d) (Succ dd) (Succ ddd) where 
	gmult (Monom a) (Monom b) = Monom $ a*b

instance (Nat v, Num a, Nat d) => GradedMult a (Succ (Succ v)) (Succ d) Zero (Succ d) where
	gmult p (Coeff s) = scalar s p
instance ( GradedMult a (Succ v) (Succ d) (Succ dd) (Succ ddd), -- 2. gmult
	GradedMult a (Succ (Succ v)) (Succ d) dd ddd,  -- 1. gmult
	GradedMultHelper a (Succ v) (Succ dd) d  ddd,  -- gmh
	Num (HomoPoly a (Succ (Succ v)) ddd) -- +
	) 
	=> GradedMult a (Succ (Succ v)) (Succ d) (Succ dd) (Succ ddd) where
	gmult p@(HSum a b) (HSum l r) = HSum (gmult p l + gmh r a) (gmult b r)


