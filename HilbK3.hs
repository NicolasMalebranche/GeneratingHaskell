{-# LANGUAGE ParallelListComp #-}

module HilbK3 where

-- Modul für Multiplikationen nach Lehn und Sorger

import Data.Array
import Data.MemoTrie
import Elementary
import K3
import LinearAlgebra
import Permutation
import Partitions
import Data.Permute
import Data.List
import qualified Data.Set as Set
import ShowMatrix
import SymmetricFunctions
import Data.Ratio
import Debug.Trace
import Control.Concurrent
import Control.Monad
import Control.Concurrent.MVar


-- CupProdukt auf symmetrisiertem A{S_n}
--cupSA :: (PartitionLambda Int, [Int]) -> (PartitionLambda Int, [Int]) -> (PartitionLambda Int, [Int]) -> K3Domain
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
	pgc = permuteGrp (pc,lc)
	res pi = if cyctau == pb then scale cupSc else 0 where 
		scale cupSc = (cupSc * partZ pa * partZ pb * length pgc) % (partZ pc * length pga * length pgb)
		tau = compose (inverse pi) pitau
		cyctau = PartLambda $ Data.List.sortBy (flip compare) $ map length $ cycles tau
		cmn = map Set.fromList $ commonOrbits pi tau
		cl = [(or,i) | or <- sortedOrbits pitau | i<-lc]
		bls r = [(or,i) | or <- sortedOrbits tau | i<-r]
		als r = [(or,i) | or <- sortedOrbits pi | i<-r]
		-- Es reicht, über die Möglichkeiten für die Eingabe zu summieren. 
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
creationInteger (pc,lc) (pi,li) = if del==0 then 0 else fromIntegral $ prod * partZ pc0 where
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
		[(nn,a):x | nn<-[1..n::Int], a <-[1..22], x<-hilbOperators(n-nn)(d-2*nn)] ++
		[(nn,23):x | nn <-[1..n], x<-hilbOperators(n-nn)(d-2*nn-2)] 

-- Baut die Indizes des symmetrischen Produkts
sym2 vs = concat [map (\v2-> (v1,v2)) (drop i vs) | v1<-vs| i<-[0..]]

cupIntegral (pc,lc) (pa,la) (pb,lb) = numerator res where
	doubBase = [(x,y) | x<-filter (\a->integerCreation a (pa,la)/=0) ( nonZero(pa,la)) , 
		y <- filter (\a->integerCreation a (pb,lb)/=0)(nonZero(pb,lb))  ]
	singBase = filter (\a->creationInteger (pc,lc) a/=0) $ nonZero(pc,lc)
	ch c (x,y) = cupSA c x y
	ci (x,y) (a,b) = integerCreation x a * integerCreation y b 
	res = sum[creationInteger (pc,lc) sb * ch sb db * ci db ((pa,la),(pb,lb)) | sb <- singBase, db <- doubBase]
	nonZero (px,lx) =  co where
		co = map ((\(a,b)->(PartLambda a,b)).unzip.Data.List.sortBy (flip compare).concat) $ combinations $ map allIn [0..23]
		allIn a = [ [(i,a)|i<-l]| PartLambda l<-map partAsLambda $ partOfWeight $ partWeight $ subpart (px,lx) a ]

cupIntegral3 = f where
 csa = memo3 cupSA
 f  (pc,lc) (pa,la) (pb,lb) (p0,l0)= numerator res where
	tripBase = [(x,y,z) | x<-filter (\a->integerCreation a (pa,la)/=0) ( nonZero(pa,la)) , 
		y <- filter (\a->integerCreation a (pb,lb)/=0)(nonZero(pb,lb)),
		z <- filter (\a->integerCreation a (p0,l0)/=0)(nonZero(p0,l0)) ]
	singBase = filter (\a->creationInteger (pc,lc) a/=0) $ nonZero(pc,lc)
	ci (x,y,z) (a,b,q) = integerCreation x a * integerCreation y b * integerCreation z q
	ch c (x,y,z) = sum [cupSA c x run * a | run <- hilbBase n d, let a = csa run y z, a/=0]
	n = partWeight pc
	d = degHilbK3 (pb,lb) + degHilbK3 (p0,l0)
	res = sum[creationInteger (pc,lc) sb * ch sb tri  * ci tri ((pa,la),(pb,lb),(p0,l0)) | sb <- singBase,tri <- tripBase]
	nonZero (px,lx) =  co where
		co = map ((\(a,b)->(PartLambda a,b)).unzip.Data.List.sortBy (flip compare).concat) $ combinations $ map allIn [0..23]
		allIn a = [ [(i,a)|i<-l]| PartLambda l<-map partAsLambda $ partOfWeight $ partWeight $ subpart (px,lx) a ]

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

b2i i = (partAsLambda$PartAlpha [i,1], [0::K3Domain,0..])
bai i = (partAsLambda$PartAlpha [i+2], 1:[0::K3Domain,0..])
b4i i = (partAsLambda$PartAlpha [i,1], 0:1:[0::K3Domain,0..])
b5i i = (partAsLambda$PartAlpha [i,1], 1:0:[0::K3Domain,0..])

-- Schreibt Multiplikationsmatrix für Produkte mit 2 Faktoren vom Grad 2
writeSym2 n = writeFile ("GAP_Code/GAP_n="++show n++"_Sym2.txt") $ showGapMat h4 sh2 m where
	m i (j1,j2) = cupIntegral i j1 j2
	h4 = reverse $ hilbBase n 4 
	sh2 = sym2$hilbBase n 2

-- Schreibt Multiplikationsmatrix für Produkte mit Faktoren von Grad 2 und 4
-- dro und tak geben Zeilenbereiche an (zum Aufteilen auf meherere Prozesse)
write24 n dro tak = writeFile ("GAP_Code/GAP_n="++show n++"_24_linesfrom" ++show dro++"_lines"++show tak++".txt") $ showGapMat h6 h24 m where
	m i (j1,j2) = cupIntegral i j1 j2
	h2 = hilbBase n 2
	h4 = hilbBase n 4 
	h6 = take tak $ drop dro $ hilbBase n 6
	h24 = [(x,y) | x<-h2, y<-h4]

myn = 4
sym3 = f where
	h4 = hilbBase myn 4 
	h6 = hilbBase myn 6
	ci = memo3 cupIntegral
	f (i,j,k) = [(r,x6) | x6 <- h6, let r = cupIntegral3 x6 i j k, r/=0]

s3 = [(i,j,k) | i<-h2, j<- h2, k<- h2, i<=j ,j<= k] where h2 = hilbBase myn 2

testSym (i,j,k) = x == sym3 (j,k,i) && x == sym3 (k,i,j) where x = sym3 (i,j,k)

writeSym3 n = do 
 done <- newEmptyMVar
 mapM_ (forkIO . writ done) range
 takeMVar done where
	block = (length s3 `div` 4) + 1
	range = ran 1 s3 where ran i x = if x == [] then [] else (i,take block x) : ran (i+1) (drop block x)
	h4 = hilbBase n 4
	h6 = hilbBase n 6
	h2 = hilbBase n 2
	s3 = [(i,j,k) | i<-h2, j<- h2, k<- h2, i<=j ,j<= k]
	ci = memo3 cupIntegral
	cup3 (i,j,k) = [cupIntegral3 x6 i j k| x6 <- h6] 
	writ done (num,syms) = do
	  writeFile ("GAP_Code/GAP_n="++show n++"_Sym3_Part" ++show num++".txt") s 
	  putMVar done () where
	  	s = concat $ intersperse ",\n" $ map (show.cup3) syms 

