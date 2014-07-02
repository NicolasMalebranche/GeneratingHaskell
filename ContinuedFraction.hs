{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor, FlexibleInstances, UndecidableInstances #-}
module ContinuedFraction where

import Data.List

data ContinuedFraction a = CF {cfList :: [a] }
	deriving (Functor, Eq)

-- Macht eine Kettenbruchentwicklung
-- floor ist eine Abrundungsroutine
-- isZero entscheidet, ob eine Zahl 0 ist
continuedFraction floor isZero x = CF $ cf x where
	cf x = f : if isZero next then [] else cf $ recip next where
		f = floor x
		next = x - f 

-- Macht einen Bruch aus dem Kettenbruch
--resolveCF :: (Integral a, Fractional b) => ContinuedFraction a -> b
resolveCF = foldr res 0 . cfList where
	res a b = a + recip b

instance Show a => Show (ContinuedFraction a) where
	show = sf 0 . cfList where
		sf i  [] = "|"
		sf i (a:r) | i>30 = ".." 
			| otherwise = show a ++ "|" ++ sf (i+1) r

instance (Num a, Ord a) => Ord (ContinuedFraction a) where
	CF (a:x) <= CF [] = a <= 0
	CF [] <= CF (a:x)= 0 <= a
	CF [] <= CF [] = True
	CF (a:x) <= CF (b:y) = a < b || (a == b && y <= x)

