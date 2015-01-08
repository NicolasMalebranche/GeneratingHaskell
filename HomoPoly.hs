{-# OPTIONS -fglasgow-exts  -XUndecidableInstances #-}
module HomoPoly where

import Data.List

-- Experimentelles Modul, um homogene Polynome zu modellieren

data Zero
data Succ n
type One = Succ Zero
type Two = Succ One

class Nat n where natToInt :: n -> Int

instance          Nat Zero     where natToInt _ = 0
instance Nat n => Nat (Succ n) where natToInt _ = 1 + natToInt (undefined::n)


data HomoPoly a v d where
	Coeff :: (Num a, Nat v) => a -> HomoPoly a v Zero
	ZPower :: (Num a, Nat d) => a -> HomoPoly a One (Succ d)
	HSum  :: (Nat v, Nat d) => 	HomoPoly a (Succ (Succ v)) 	d 	 	 -> 
								HomoPoly a (Succ v)			(Succ d) -> 
								HomoPoly a (Succ (Succ v)) 	(Succ d) 

-- Beispiele
bsp1 = HSum (Coeff 1) (ZPower 1) -- y+z
bsp2 = HSum bsp1 (ZPower 1) -- y²+yz+z²
bsp3 = HSum (Coeff 1) bsp1  -- x+y+z
bsp4 = HSum bsp3 $ HSum bsp1 $ ZPower 1 -- x²+y²+z²+xy+xz+yz

class HP p where 
	pvar :: p -> Int
	pdeg :: p -> Int

instance (Nat v, Nat d) => HP (HomoPoly a v d) where
	pvar _ = natToInt (undefined :: v)
	pdeg _ = natToInt (undefined :: d)


instance (Eq a,Nat v) => Eq (HomoPoly a v Zero) where
	Coeff a == Coeff b = a==b
instance (Eq a,Nat d) => Eq (HomoPoly a One (Succ d)) where
	ZPower a == ZPower b = a==b
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
	fromInteger i = ZPower 0
	negate (ZPower a ) = ZPower $ negate a
	(+) (ZPower a) (ZPower b) = ZPower (a+b)
	abs = undefined
	signum = undefined
	(*) = undefined

instance (Num a, Nat v, Nat d, Num (HomoPoly a (Succ v) (Succ d)), Num (HomoPoly a (Succ (Succ v)) d)) 
	=>	Num (HomoPoly a (Succ (Succ v)) (Succ d)) where
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
mono m@(ZPower a) = [reverse $ show a ++ replicate (pdeg m) 'z']
mono (HSum l r) = map ((:) (['{','z'..]!!pvar l)) (mono l) ++ mono r

-- Zum Multiplizieren : gmult
scalar :: Num a => a -> HomoPoly a v d -> HomoPoly a v d
scalar a (Coeff b) = Coeff $ a*b
scalar a (ZPower b) = ZPower $ a*b
scalar a (HSum l r) = HSum (scalar a l) (scalar a r)

addVariable :: (Num a, Nat v, Nat d, Num (HomoPoly a (Succ v) d )) 
	=> HomoPoly a v (Succ d) -> HomoPoly a (Succ v) (Succ d) 
addVariable m@(ZPower _) = HSum 0 m
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
	gmh (ZPower a) (Coeff s) =  HSum 0 (ZPower $ a*s)
instance (Num a, GradedMultHelper a One (Succ d) dd ddd) 
	=> GradedMultHelper a One (Succ d) (Succ dd) (Succ ddd) where
	gmh m@(ZPower a) (HSum l (ZPower b)) = HSum (gmh m l) (ZPower $ a*b)

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
	gmult (ZPower a) (Coeff s) = ZPower $ a*s
instance (Num a, Nat d, Nat ddd, GradedMult a One (Succ d) dd ddd ) 
	=> GradedMult a One (Succ d) (Succ dd) (Succ ddd) where 
	gmult (ZPower a) (ZPower b) = ZPower $ a*b

instance (Nat v, Num a, Nat d) => GradedMult a (Succ (Succ v)) (Succ d) Zero (Succ d) where
	gmult p (Coeff s) = scalar s p
instance ( GradedMult a (Succ v) (Succ d) (Succ dd) (Succ ddd), -- 2. gmult
	GradedMult a (Succ (Succ v)) (Succ d) dd ddd,  -- 1. gmult
	GradedMultHelper a (Succ v) (Succ dd) d  ddd,  -- gmh
	Num (HomoPoly a (Succ (Succ v)) ddd) -- +
	) 
	=> GradedMult a (Succ (Succ v)) (Succ d) (Succ dd) (Succ ddd) where
	gmult p@(HSum a b) (HSum l r) = HSum (gmult p l + gmh r a) (gmult b r)


