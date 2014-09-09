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
import qualified Data.IntMap as IntMap
import qualified Math.LinearAlgebra.Sparse.Matrix as Sparse


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
integerCreation  (pc,lc) (pi,li)= if del==0 then 0 else prod / fromIntegral (partZ pc0) where
	prod = product [powerMonomial (subpart (pi,li) a) (subpart (pc,lc) a) | a<-[1..22]]
	(pc0,pi0) = (subpart (pc,lc) 0 , subpart (pi,li) 0)
	(pcz,piz) = (subpart (pc,lc) 23, subpart (pi,li)23)
	del = delta pc0 pi0 * delta pcz piz

-- Ganzzahlige Basis nach Qin / Wang
-- creation = creationInteger * integerBase
creationInteger (pi,li) (pc,lc) = if del==0 then 0 else fromIntegral $ prod * partZ pc0 where
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

cupIntegral (pc,lc) (pa,la) (pb,lb) = toInt res where
	doubBase = [(x,y) | x<-filter (\a->integerCreation a (pa,la)/=0) ( nonZero(pa,la)) , 
		y <- filter (\a->integerCreation a (pb,lb)/=0)(nonZero(pb,lb))  ]
	singBase = filter (\a->creationInteger (pc,lc) a/=0) $ nonZero(pc,lc)
	ch c (x,y) = cupSA c x y
	ci (x,y) (a,b) = integerCreation x a * integerCreation y b 
	res = sum[creationInteger (pc,lc) sb * ch sb db * ci db ((pa,la),(pb,lb)) | sb <- singBase, db <- doubBase]
	nonZero (px,lx) =  co where
		co = map ((\(a,b)->(PartLambda a,b)).unzip.Data.List.sortBy (flip compare).concat) $ combinations $ map allIn [0..23]
		allIn a = [ [(i,a)|i<-l]| PartLambda l<-map partAsLambda $ partOfWeight $ partWeight $ subpart (px,lx) a ]

-- Ergibt Liste mit Nicht-Null Elementen
cupSAsp n deg = cl where
	base = hilbBase n deg
	cl ((pa,la),(pb,lb)) = [((pc,lc),x) | (pc,lc) <- base, check pc pa pb lc la lb, let x = cupSA (pc,lc) (pa,la) (pb,lb), x/=0]
	check (PartLambda c) (PartLambda a) (PartLambda b) lc la lb = u && v  where
		ac = all(==1) c; aa = all(==1) a; ab=all(==1) b
		u = if ac then a==b else if ab then a==c  else if aa then b==c else True
		v = if ab && aa && all (/=23) lc then take n (Data.List.sortBy(flip compare)(la++lb))==lc else True

-- Hilfsfunktion: Filtert Erzeugerkompositionen
subpart (PartLambda pl,l) a = PartLambda $ sb pl l where
	sb [] _ = []
	sb pl [] = sb pl [0,0..]
	sb (e:pl) (la:l) = if la == a then e: sb pl l else sb pl l

-- Schreibt Multiplikationsmatrix für Produkte mit 2 Faktoren vom Grad 2
writeSym2 n = writeFile ("GAP_Code/GAP_n="++show n++"_Sym2.txt") $ showGapMat h4 sh2 m where
	m i (j1,j2) = cupIntegral i j1 j2
	h4 = reverse $ hilbBase n 4 
	sh2 = sym2$hilbBase n 2

-- Schreibt Multiplikationsmatrix für Produkte mit Faktoren von Grad 2 und 4
-- dro und tak geben Zeilenbereiche an (zum Aufteilen auf meherere Prozesse)
write24 n = writeFile ("GAP_Code/GAP_n="++show n++"_24'.txt")  m where
	m = "a:= [\n" ++ concat (intersperse",\n"[show$col y4 y2 |y4<-h4,y2<-h2] ) ++"\n];;\n"
	h2 = hilbBase n 2
	h4 = hilbBase n 4 
	h6 = hilbBase n 6
	cup = cupSAsp n 6
	ic = memo2 integerCreation
	ic4 = memo i where i y4 = [(x4,u) | x4<-h4, let u = integerCreation x4 y4, u/=0]
	base2 y2 y4 = [((x2,x4),u*v) | (x4,u) <- ic4 y4,  x2<-h2, let v=ic x2 y2, v/=0]
	cup2 y2 y4 = sumSparse [mult uv $ cup x24 | (x24,uv) <- base2 y2 y4]  
	mult alpha = map (\(a,v)->(a,alpha*v))
	col y2 y4 = [z| y6<-h6,let z = toInt$sum [z*creationInteger y6 x6 | (x6,z) <- cup2 y2 y4] ]


sumSparse = foldr somme [] where
	somme a [] = a
	somme [] b = b
	somme a@((aa,va):ra) b@((bb,vb):rb) | aa==bb = (aa,va+vb):somme ra rb
		| aa < bb = (aa,va):somme ra b
		| otherwise=(bb,vb):somme a rb


toInt q = if n ==1 then z else if (z `div` n)*n==z then (z`div`n) else 7777777 where (z,n) =(numerator q, denominator q)

writeSym3 n = writeFile ("GAP_Code/GAP_n="++show n++"_Sym3'.txt") s where
	h2 = hilbBase n 2; h4 = hilbBase n 4; h6 = hilbBase n 6
	h222 = [(i,j,k)| i<-h2, j<-h2, i<=j, k<-h2, j<=k]
	mult alpha = map (\(a,v)->(a,alpha*v))
	csaSP = cupSAsp n 6
	cup3 (n,m,l) = sumSparse [mult c2 $ csaSP (l,p) | p<-h4, let c2=cup2 p n m, c2 /= 0]	
	cup2 = memo3 cupSA
	ic = memo2 integerCreation
	base3 (i,j,k) = [((n,m,l),x*y*z)|n<-h2,let x=ic n i,x/=0, m<-h2,let y=ic m j, y/=0, l<-h2, let z=ic l k, z/=0]
	icup3 ijk = sumSparse [mult xyz $ cup3 nml | (nml,xyz)<-base3 ijk ]
	line (i,j,k) = [toInt$sum [v*creationInteger r q|(q,v)<-icup3(i,j,k)]| r<-h6]
	s = "a := [\n" ++ concat(intersperse ",\n" [show $line ijk | ijk<-h222]) ++"\n];;\n"
