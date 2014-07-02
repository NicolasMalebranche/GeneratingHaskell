module Permutation where

import Data.Permute
import Partitions
import Data.List

compose s t = swapsPermute (max (size s) (size t)) (swaps s ++ swaps t)

-- Bestimmt die Orbits der von pi und tau erzeugten Gruppe
commonOrbits pi tau = foldr (uni [][]) (cycles pi) (cycles tau) where
	uni i ni c []  = i:ni
	uni i ni c (k:o) = if Data.List.intersect c k == [] 
		then uni i (k:ni) c o else uni (i++k) ni c o

-- Bestimmt die Verklebedaten der Orbits der von pi und tau erzeugten Gruppe
uniCyc pi tau = foldr (f ([],[])[])  [([],[d]) | d <- cycles pi] (cycles tau) where
	f (ci,di) ni c [] = (c:ci,di) : ni
	f (ci,di) ni c ((ck, dk):r) = 
		if all (==[]) $ [Data.List.intersect c d | d<-dk] 
		then f (ci,di) ((ck,dk):ni) c r 
		else f (ci++ck, di++dk) ni c r

-- Sortierte Zykel, absteigend der Länge nach
sortCycles pi = Data.List.sortBy f $ cycles pi where f a b = compare (length b) (length a)

-- 

refp = listPermute 5 [1,0,3,4,2]
refq = listPermute 5 [4,1,2,0,3]