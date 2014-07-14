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
import SymmetricFunctions

-- Cup Produkt für Produkte von Erzeugungsoperatoren
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

-- Ganzzahlige Basis nach Qin / Wang
-- integerBase = integerCreation * creation
integerCreation (pi,li) (pc,lc) = if del==0 then 0 else prod / fromIntegral (partZ pc0) where
	prod = product [powerMonomial (subpart (pi,li) a) (subpart (pc,lc) a) | a<-[1..22]]
	(pc0,pi0) = (subpart (pc,lc) 0 , subpart (pi,li) 0)
	(pcz,piz) = (subpart (pc,lc) 23, subpart (pi,li)23)
	del = delta pc0 pi0 * delta pcz piz

-- Ganzzahlige Basis nach Qin / Wang
-- creation = creationInteger * integerBase
creationInteger (pc,lc) (pi,li) = if del==0 then 0 else prod * partZ pc0 where
	prod = product [monomialPower (subpart (pc,lc) a) (subpart (pi,li) a) | a<-[1..22]]
	(pc0,pi0) = (subpart (pc,lc) 0 , subpart (pi,li) 0)
	(pcz,piz) = (subpart (pc,lc) 23, subpart (pi,li)23)
	del = delta pc0 pi0 * delta pcz piz

-- Hilfsfunktion: Filtert Erzeugerkompositionen
subpart (PartLambda pl,l) a = PartLambda $ sb pl l where
	sb [] _ = []
	sb pl [] = sb pl [0,0..]
	sb (e:pl) (la:l) = if la == a then e: sb pl l else sb pl l

p211 = PartLambda [2,1,1::Int]
p31 = PartLambda [3,1::Int]
p4 = PartLambda [4::Int]
p22 = PartLambda [2,2::Int]