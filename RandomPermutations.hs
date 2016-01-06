module RandomPermutations where

import Data.Permute
import Partitions
import Elementary
import Data.MemoTrie
import Data.List
import Data.Ratio
import PrimeFactors

perms = memo p where
	p n = permute n : unfoldr (fmap (\x -> (x,x)).next) (permute n)

mults = memo m where
	m n = [ (a,b,swapsPermute n $ swaps a ++ swaps b) | a <- perms n, b<-perms n]

-- Wahrscheinlichkeit, daß Prädikat pred zutrifft
p n pred = a % (factorial n)^2 where 
	a = length $ filter pred $ mults n

-- Bedingte Wahrscheinlichkeit
b n pred bed = a % length rest where
	rest = filter bed $ mults n
	a = length $ filter pred rest

-- Erwartungswert
estimate n f = sum [ f x | x <- mults n] % factorial n ^ 2

-- schaut nach, ob der Zykel, in dem i enthalten ist, gleich lang bleibt
-- p n $ cycleSameLength 0 = 1/n
cycleSameLength i (a,b,c) = l a == l c where
	l x = head [ length c| c <- cycles x, i `elem` c]

-- schaut nach, ob Permutation an erster Stelle vom Zykeltyp alpha ist
hasShapeA alpha (a,b,c) = cycleType a == alpha

-- schaut nach, ob Permutation a Permutation c dominiert, wenn a b dominiert
dominates (a,b,c) = not(partDominates ca cb) || partDominates ca cc where
	[ca,cb,cc] = map cycleType [a,b,c]

-- Länge des Zykels, in dem 0 enthalten ist
-- estimate n lengthCA = (n+1)/2
lengthCA (a,b,c) = l a where
	l x = head [ length c| c <- cycles x, 0 `elem` c]

