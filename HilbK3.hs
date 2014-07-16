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
	pitau = partPermute pc
	sortedOrbits pi = Data.List.sortBy (flip compare) $ map Set.fromList $ cycles pi
	permuteGrp (PartLambda l, a) = map concat $ symmetrize $
		map (snd . unzip) $ groupBy (\a b -> fst a==fst b) $ zip l a
	symmetrize [] = [[]]
	symmetrize (l:r) = [pl : a | a <- symmetrize r, pl <- nub $ permutations l]
	-- Möglichkeiten, die Klassen den Orbits zuzuordnen
	pga = permuteGrp (pa,la)
	pgb = permuteGrp (pb,lb)
	res pi = if cyctau == pb then cupSc else 0 where 
		tau = compose (inverse pi) pitau
		cyctau = PartLambda $ Data.List.sortBy (flip compare) $ map length $ cycles tau
		cmn = map Set.fromList $ commonOrbits pi tau
		cl = [(or,i) | or <- sortedOrbits pitau | i<-lc]
		bls r = [(or,i) | or <- sortedOrbits tau | i<-r]
		als r = [(or,i) | or <- sortedOrbits pi | i<-r]
		-- Es reicht, über die Möglichkeiten für die Eingabe zu sortieren. 
		cupSc = sum [ cupSym cl cmn (als pla) (bls plb) | pla<-pga, plb<-pgb]


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
-- Achtung: Koffizienten sind nur rational!
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

degHilbK3 (lam,a) = 2*partDegree lam + sum [degK3 i | i<- a]

-- Basis von Hilb^n(K3) vom Grad d 
hilbBase n d = map ((\(a,b)->(PartLambda a,b)).unzip) $ hilbOperators n d  

-- Alle möglichen Kombinationen von Erzeugungsoperatoren von 
-- Gewicht n und Grad d
hilbOperators = memo2 hb where 
	hb 0 0 = [[]] --Leeres Operatorprodukt
	hb n d = if n<0 || odd d || d<0 then [] else 
		nub $ map (Data.List.sortBy (flip compare)) $ f n d
	f n d = [(nn,0):x | nn <-[1..n], x<-hilbOperators(n-nn)(d-2*nn+2)] ++
		[(nn,a):x | nn<-[1..n::Int], a <-[1..2], x<-hilbOperators(n-nn)(d-2*nn)] ++
		[(nn,23):x | nn <-[1..n], x<-hilbOperators(n-nn)(d-2*nn-2)] 

-- Baut die Indizes des symmetrischen Produkts
sym2 vs = concat [map (\v2-> (v1,v2)) (drop i vs) | v1<-vs| i<-[0..]]

cupIntegral (pc,lc) (pa,la) (pb,lb) = res where
	(nc,dc) = (partWeight pc, degHilbK3 (pc,lc))
	(na,da) = (partWeight pa, degHilbK3 (pa,la))
	(nb,db) = (partWeight pb, degHilbK3 (pb,lb))
	doubBase = [(x,y) | x<- hilbBase na da , y <- hilbBase nb db ]
	ch c (x,y) = cupHilb c x y
	ci (x,y) (a,b) = creationInteger x a * creationInteger y b -- CreationInteger austauschen?
	m1 = mM doubBase ch ci
	m1R i j = fromIntegral $ m1 i j
	m2 = mM (hilbBase nc dc) integerCreation m1R 
	res = m2 (pc,lc) ((pa,la),(pb,lb))


-- Hilfsfunktion: Filtert Erzeugerkompositionen
subpart (PartLambda pl,l) a = PartLambda $ sb pl l where
	sb [] _ = []
	sb pl [] = sb pl [0,0..]
	sb (e:pl) (la:l) = if la == a then e: sb pl l else sb pl l

p211 = fst b211 
p22 = fst b22
p31 = fst b31
p3 = fst b3
p21 = fst b21
b211 = (PartLambda [2,1,1::Int] , [0,0,0::K3Domain])
b31 = (PartLambda [3,1::Int] , [0,0::K3Domain])
b22 = (PartLambda [2,2::Int] , [0,0::K3Domain])
b3 = (PartLambda [3::Int] , [0::K3Domain])
b21= (PartLambda [2,1::Int] , [0,0::K3Domain])