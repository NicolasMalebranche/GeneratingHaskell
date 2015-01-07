{-# OPTIONS -fglasgow-exts  -XUndecidableInstances #-}
module HomoPoly where

import Data.List

-- Experimentelles Modul, um homogene Polynome zu modellieren

data Zero
data Succ n

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


data HomoPoly a v d where
	Coeff :: (Num a, Nat v) => a -> HomoPoly a v Zero
	Monom :: (Num a, Nat d) => a -> HomoPoly a (Succ Zero) d
	HSum  :: (Nat v, Nat d) => HomoPoly a (Succ v) d -> HomoPoly a v (Succ d) -> HomoPoly a (Succ v) (Succ d) 

class HP p where 
	pvar :: p -> Int
	pdeg :: p -> Int

instance (Nat v, Nat d) => HP (HomoPoly a v d) where
	pvar _ = natToInt (undefined :: v)
	pdeg _ = natToInt (undefined :: d)

--instance Functor (Hom

instance (Eq a,Nat v) => Eq (HomoPoly a v Zero) where
	Coeff a == Coeff b = a==b
instance (Eq a,Nat d) => Eq (HomoPoly a (Succ Zero) (Succ d)) where
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

instance (Num a,Nat d) => Num (HomoPoly a (Succ Zero) (Succ d)) where
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
class GradedMult p q pq | p q -> pq, p pq -> q where 
	gmult :: p -> q -> pq

--instance (Num a, Nat v, Nat d) => GradedMult (HomoPoly a v Zero) (HomoPoly a v d) (HomoPoly a v d) where
--	gmult (Coeff  








