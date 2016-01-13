module LieAlgebra where

import Algebra
import Data.List

-- Sachen mit Lieklammer
class Ord a => LieAlgebra a where
	lie :: Num z => a -> a -> [(a,z)]

-- lieFoldR z [a,b,c..] = [a,[b,[c,..,z]]]
lieFoldR z [] = [(z,1)]
lieFoldR z (a:r) = algNub [ (c,x*y) | (b,x) <- lieFoldR z r, (c,y) <- lie a b]

-- lieFoldL z [a,b,c..] = [[[z,a],b],c..]
lieFoldL z [] = [(z,1)]
lieFoldL z (a:r) = algNub [ (c,x*y) | (b,x) <- lie z a, (c,y) <- lieFoldL b r ]

-- Potenz der Adjunktion
lieAd a n = flip lieFoldR [ a | i<-[1..n]] 

