{-# LANGUAGE TypeFamilies, EmptyDataDecls, FlexibleContexts, 
			  UndecidableInstances  #-}
module ZechPrimeField where

import F_p
import Data.Array
import Data.List

-- Zechscher Logarithmus
zechLog :: (Ord f, FiniteField f) => f -> Array Int Int
zechLog primRoot = array (0,q_2) $ zip (map snd a) (map snd b) where
	q_2 = ffOrder primRoot - 2
	rang = range (0,q_2)
	powers = 1 : map (primRoot *) powers
	a = sortBy ((.fst).compare.fst) $ zip (map (1+)powers) rang
	b = sortBy ((.fst).compare.fst) $ zip powers rang
