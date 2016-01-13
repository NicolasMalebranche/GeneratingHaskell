-- Stellt Methoden zur Berechnung von formalen Summen bereit
module Algebra where

import Data.List

-- Algebraisches Nub
algNub [] = []
algNub l = sn (head sl) (tail sl) where
	sl = sortBy ((.fst).compare.fst) l
	sn (i,x) ((j,y):r) = if i==j then sn (i,x+y) r else app (i,x) $ sn (j,y) r
	sn ix [] = app ix []
	app (i,x) r = if x==0 then r else (i,x) : r

-- Skalierung
algScal 0 _ = []
algScal a l = [ (p,a*x) | (p,x) <- l]

-- Summe 
algSum list = algNub $ foldr (++) [] list

class Ord a => Algebra a where
	algMult :: Num z => a -> a -> [(a,z)]

