{-# LANGUAGE ScopedTypeVariables #-}
module ZechPrimeField where

import F_p
import F_q
import Data.Array
import Data.List
import Data.Ratio


newtype ZechTable a = ZechTable (Array Int Int)
newtype Zech a = Zech Int

class ZechField a where
	zechTable :: ZechTable a
	zechO :: a -- ein bißchen mißbräuchlich
	zechE :: a -- = -1


-- Zechscher Logarithmus
zechLog :: (Ord f, FiniteField f) => f -> Array Int Int
zechLog primRoot = array (i,q_2) $ zip (map snd a) (map snd b) where
	i = -1
	q_2 =  ffOrder primRoot - 2
	rang = range ( 0,q_2)
	powers = 1 : map (primRoot *) powers
	a = sortBy ((.fst).compare.fst) $ (1,i) : zip (map (1+)powers) rang
	b = sortBy ((.fst).compare.fst) $ (0,i) : zip powers rang


fromZech (Zech (-1)) = 0
fromZech (Zech i :: Zech f) = (primRoot::f)^i 

toZech a = z where
	Just z = find ((==) a . fromZech) ffAll

instance (Ord f, FiniteField f) => ZechField (Zech f) where
	zechTable = ZechTable $ zechLog (primRoot :: f)
	zechO = Zech $ ffOrder (primRoot :: f)
	zechE = Zech (if odd o then div (o-1) 2 else 0) where
		o = ffOrder (primRoot :: f)

instance Eq (Zech a) where
	Zech a == Zech b = a == b

instance Ord (Zech a) where
	compare (Zech a) (Zech b) = compare a b


instance (Ord f, FiniteField f) => Show (Zech f) where
	show = \(Zech i) -> if i == -1 then "0" else 
		"Z" ++ show o ++"^" ++ show i where
		Zech o = zechO :: Zech f


instance (Ord f, FiniteField f) => Num (Zech f) where
	Zech (-1) + b = b 
	a + Zech (-1) = a
	Zech i + Zech j = let
		ZechTable t = zechTable :: ZechTable (Zech f)
		Zech o = zechO :: Zech f
		za a (-1) = -1
		za a b = mod (a+b) (o-1) 
		in Zech $ if i<j then za i $ t!(j-i) else za j $ t!(i-j)
	negate = (*) zechE
	Zech (-1) * b = Zech (-1) 
	a * Zech (-1) = Zech (-1)
	Zech i * Zech j = Zech $ mod (i+j) (o-1) where 
		Zech o = zechO :: Zech f
	fromInteger 1 = Zech 0
	fromInteger 0 = Zech (-1)
	fromInteger (-1) = zechE
	fromInteger i = toZech $ fromInteger i
	abs = undefined
	signum = undefined
	

instance (Ord f, FiniteField f) => Fractional (Zech f) where
	fromRational q = fromInteger (numerator q) / fromInteger (denominator q)
	a / Zech (-1) = error "Zech: Division by zero"
	Zech (-1) / b = Zech (-1) 
	Zech i / Zech j = Zech $ mod (i-j) (o-1) where 
		Zech o = zechO :: Zech f
	recip (Zech (-1)) = error "Zech: Division by zero"
	recip (Zech i) = Zech $ mod (-i) (o-1) where
		Zech o = zechO :: Zech f

instance (Ord f, FiniteField f) => FiniteField (Zech f) where
	primRoot = Zech 1
	ffAll = a where
		a = map Zech [-1 .. ffOrder (head a) - 2]
	ffOrder _ = ffOrder (undefined :: f)
	ffChar _ = ffChar (undefined :: f)



