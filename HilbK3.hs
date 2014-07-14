{-# LANGUAGE ParallelListComp #-}

module HilbK3 where

-- Modul für Multiplikationen nach Lehn und Sorger

import Data.Array
import Data.MemoTrie
import K3
import LinearAlgebra
import Permutation
import Partitions
import Data.Permute
import Data.List
import qualified Data.Set as Set

cupHilb (pc,lc) (pa,la) (pb,lb) = if isZero then 0 else res where
	(wa,wb,wc) =(partWeight pa,partWeight pb,partWeight pc)
	isZero = wa/=wb || wb/= wc
	res = cupSA (pc,lc) (pa,la) (pb,lb) * factorial wa

-- CupProdukt auf symmetrisiertem A{S_n}
cupSA :: (PartitionLambda Int, [Int]) -> (PartitionLambda Int, [Int]) -> (PartitionLambda Int, [Int]) -> K3Domain
cupSA (pc,lc) (pa,la) (pb,lb) = sum [res pi | pi <- partAllPerms pa] where
	tau = partPermute pb
	sortedOrbits pi = Data.List.sortBy (flip compare) $ map Set.fromList $ cycles pi
	res pi = if cycpitau == pc then cupSc else 0 where 
		pitau = compose pi tau
		cycpitau = PartLambda $ Data.List.sortBy (flip compare) $ map length $ cycles pitau
		cmn = map Set.fromList $ commonOrbits pi tau
		cl = [(or,i) | or <- sortedOrbits pitau | i<-lc]
		bl = [(or,i) | or <- sortedOrbits tau | i<-lb]
		al = [(or,i) | or <- sortedOrbits pi | i<-la]
		cupSc = cupSym cl cmn al bl

-- Multiplikation in Lehn & Sorgers A{S_n}
-- Ausgabe -> Gemeinsame Orbits -> Eingabe1 -> Eingabe2 -> Faktor
-- Ausgabe, Eingabe1 und Eingabe2 müssen alle feiner partitioniert sein als Gemeinsame Orbits
cupSym :: [(Set.Set Int, Int)] -> [Set.Set Int] -> [(Set.Set Int, Int)] -> [(Set.Set Int, Int)] -> K3Domain
cupSym cList commonOrbits aList bList = product [ sum (x o) | o <- commonOrbits ] where
	x o = [cupAdL xc delta * cupL delta cupList * (euler!23)^defekt | delta <- [0..23]] where
		xa = [af | (aOr,af) <- aList, Set.isSubsetOf aOr o]
		xb = [bf | (bOr,bf) <- bList, Set.isSubsetOf bOr o]
		xc = [cf | (cOr,cf) <- cList, Set.isSubsetOf cOr o]
		cupList = xa ++ xb ++ replicate defekt 23
		defekt = div (Set.size o + 2 - length xa - length xb - length xc) 2

mya = [(Set.fromList[1,2],0),(Set.fromList[3],0)]:: [(Set.Set Int, Int)] 
myb = [(Set.fromList[2,3],0),(Set.fromList[1],0)]:: [(Set.Set Int, Int)] 
myc = [(Set.fromList[1,2,3],0)]:: [(Set.Set Int, Int)] 
cmn = [Set.fromList[1,2,3]]:: [Set.Set Int] 


p211 = PartLambda [2,1,1::Int]
p31 = PartLambda [3,1::Int]
p4 = PartLambda [4::Int]
p22 = PartLambda [2,2::Int]