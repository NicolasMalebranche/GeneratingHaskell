module ZechPrimeField where

import F_p
import Data.Array
import Data.List

newtype ZechExp = Zech Int deriving (Eq,Ord,Ix,Show)


-- Zechscher Logarithmus
zechLog :: (Ord f, FiniteField f) => f -> Array ZechExp ZechExp
zechLog primRoot = array (i,q_2) $ zip (map snd a) (map snd b) where
	i = Zech $ -1
	q_2 = Zech $ ffOrder primRoot - 2
	rang = range (Zech 0,q_2)
	powers = 1 : map (primRoot *) powers
	a = sortBy ((.fst).compare.fst) $ (1,i) : zip (map (1+)powers) rang
	b = sortBy ((.fst).compare.fst) $ (0,i) : zip powers rang



