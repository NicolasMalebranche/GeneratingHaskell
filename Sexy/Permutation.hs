module Permutation where

import Data.Permute
import Partitions
import Data.List
import qualified Data.Set as Set

compose s t = swapsPermute (max (size s) (size t)) (swaps s ++ swaps t)

-- Bestimmt die Orbits der von pi und tau erzeugten Gruppe
commonOrbits pi tau = Data.List.sortBy (\a b -> compare (length b)(length a)) orl where
	orl = foldr (uni [][]) (cycles pi) (cycles tau) 
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

-- Das Ganze mit Mengen
orbits pi = Set.fromList $ map Set.fromList $ cycles pi

-- Bestimmt Verklebedaten [([Orbits von pi], Orbit von pi,tau)]
glueOrbits pi tau = foldr (f ([],Set.empty)[]) init (map Set.fromList $ cycles pi) where
	init = [([],Set.fromList d) | d <- cycles tau] 
	f (ci,di) ni c [] = (c:ci,di) : ni
	f (ci,di) ni c ((ck, dk):r) = 
		if Set.null $ Set.intersection c dk
		then f (ci,di) ((ck,dk):ni) c r 
		else f (ci++ck, Set.union di dk) ni c r

-- Bestimmt Verklebedaten [([Orbits von pi], [Orbits von tau], Orbit von pi,tau)]
glueOrbits2 pi tau = foldr (f ([],[],Set.empty)[]) init (map Set.fromList $ cycles pi) where
	init = [([],[Set.fromList d],Set.fromList d) | d <- cycles tau] 
	f (ci,fi,di) ni c [] = (c:ci,fi,di) : ni
	f (ci,fi,di) ni c ((ck, fk, dk):r) = 
		if Set.null $ Set.intersection c dk
		then f (ci,fi,di) ((ck,fk, dk):ni) c r 
		else f (ci++ck, fi++fk, Set.union di dk) ni c r

-- Graph Defekt. b muß ein gemeinsamer Orbit von pi, tau sein
defect pi tau b = div def 2 where
	def = Set.size b + 2 - Set.size pior - Set.size tauor - Set.size pitauor
	myfilt = Set.filter $ not. Set.null . Set.intersection b
	pior = myfilt $orbits pi
	tauor = myfilt $ orbits tau
	pitauor = myfilt $ orbits $ compose pi tau

graphDefect or1 or2 or3 b = div def 2 where
	def = Set.size b + 2 - Set.size bor1 - Set.size bor2 - Set.size bor3
	myfilt = Set.filter $ not. Set.null . Set.intersection b
	bor1 = myfilt or1
	bor2 = myfilt or2
	bor3 = myfilt or3

refp = listPermute 5 [1,0,3,4,2]
refq = listPermute 5 [0,1,2,4,3]