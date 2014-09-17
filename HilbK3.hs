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
import Data.Permute hiding (sort,sortBy)
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

type AnBase = (PartitionLambda Int, [K3Domain])
type SnBase = [([Int],K3Domain)]

anZ :: AnBase -> Int
anZ (PartLambda l, k) = comp 1 (0,undefined) 0 $ zip l k where
	comp acc old m (e@(x,_):r) | e==old = comp (acc*x) old (m+1) r
		| otherwise = comp (acc*x*fac m) e 1 r
	comp acc _ m [] = fac m * acc
	fac n = if n==0 then 1 else n*fac(n-1)

-- (Partition,[Klasse]) geht auf ([[(Zykel,Klasse)]],Multiplizitaet)
-- gibt die symmetrisierte Interpretation in A{S_n} zurueck
toSn :: AnBase -> ([SnBase],Int)
toSn =  makeSn where
	shape l = (map (forth IntMap.!) l, IntMap.fromList $ zip [1..] sl) where
		sl = map head$ group $ sort l; 
		forth = IntMap.fromList$ zip sl [1..]
	symmetrize :: (PartitionLambda Int, [K3Domain])-> ([[([Int],K3Domain)]],Int)
	symmetrize (part,l) = (perms, toIntStrict $ SymmetricFunctions.factorial n% length perms)  where 
		perms = nub [sortSn$ zipWith (\c cb ->(ordCycle $ map(p!)c, cb) ) cyc l | p <- allPerms n]
		cyc = sortBy ((.length).flip compare.length) $ cycles $ partPermute part
		n = partWeight part
	ordCycle cyc = take l $ drop p $ cycle cyc where
		(m,p,l) = foldl findMax (-1,-1,0) cyc
		findMax (m,p,l) ce = if m<ce then (ce,l,l+1) else (m,p,l+1)
	sortSn = sortBy	compareSn  where
		compareSn (cyc1,class1) (cyc2,class2) = let
			cL = compare l2 $ length cyc1 ; l2 = length cyc2
			cC = compare class2 class1
			in if cL /= EQ then cL else if cC /= EQ then cC else compare cyc2 cyc1  
	mSym = memo symmetrize
	makeSn (part,l) = ([ [(z,im IntMap.! k) | (z,k) <- op ]|op <- res],m)  where
		(repl,im) = shape l
		(res,m) = mSym (part,repl)
-- Kleiner Check
check_toSn = foldr (&&) True [snd (toSn p) == anZ p | p <- hilbBase 6 6 ]

-- Multipliziert zwei Permutationen mit angehefteten Klassen	
multSn :: SnBase -> SnBase -> [(SnBase,Int)]
multSn l1 l2 = tensor $ map m cmno where
	pi1 = cyclesPermute n $ cy1 ; cy1 = map fst l1; n = sum $ map length cy1
	pi2 = cyclesPermute n $ map fst l2
	set1 = map (\(a,b)->(Set.fromList a,b)) l1; set2 = map (\(a,b)->(Set.fromList a,b)) l2
	tau = compose pi1 pi2
	cyt = cycles tau ; 
	cmno = map Set.fromList $ commonOrbits pi1 pi2; 
	m or = fdown where
		sset12 = [xv | xv <-set1++set2, Set.isSubsetOf (fst xv) or]
		fup = cupLSparse $ map snd sset12 ++ replicate def 23 
		t = [c | c<-cyt, Set.isSubsetOf (Set.fromList c) or]
		fdown = [(zip t l,v*w*24^def)| let [(r,v)] = fup, (l,w)<-cupAdLSparse(length t) r ]-- TODO: exhaustive Pattern match 
		def = toIntStrict ((Set.size or + 2 - length sset12 - length t)%2)
	tensor [] = [([],1)]
	tensor (t:r) = [(y++x,w*v) |(x,v)<-tensor r, (y,w) <- t ]

-- Multipliziert zwei Paare (PartLambda Int,[K3Domain])
multAn :: AnBase -> AnBase -> [(AnBase,Int)]
multAn a = multb where
	(asl,m) = toSn a
	toAn sn =(PartLambda l, k) where (l,k)= unzip$ sortBy (flip compare)$ map (\(c,k)->(length c,k)) sn
	multb (pb,lb) = map ungroup$ groupBy ((.fst).(==).fst) $sort elems where
		ungroup g@((an,_):_) = (an, sum $ map snd g )
		bs = zip (cycles $ partPermute pb) lb
		elems = [(toAn cs,v) | as <- asl, (cs,v) <- multSn as bs]
		

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



allPerms = memo p where p n = map (array (0,n-1). zip [0..]) (Data.List.permutations [0..n-1]) 	

mcupSA ((pa,la),(pb,lb)) = sumUp $concat $ map multiply symcycB   where
	n = partWeight pa
	degA = degHilbK3 (pa,la); degB = degHilbK3 (pb,lb)
	perA = partPermute pa; perB = partPermute pb
	cycB = sortBy ((.length).flip compare.length) (cycles perB)
	orbA = zip (sortBy (flip compare) $ map Set.fromList $ cycles perA) la
	-- Konjugiert mit allen Permutationen
	symcycB = [ map (map (p!)) cycB | p <- allPerms n]
	symB = map (\x -> (head x, length x)) $ group $ sort perms  where 
		perms = [sortSn$ zipWith (\c cb ->(ordCycle $ map(p!)c, cb) ) cycB lb | p <- allPerms n]
	ordCycle cyc = take l $ drop p $ cycle cyc where
		(m,p,l) = foldl findMax (-1,-1,0) cyc
		findMax (m,p,l) ce = if m<ce then (ce,l,l+1) else (m,p,l+1)
	sortSn = sortBy	compareSn  where
		compareSn (cyc1,class1) (cyc2,class2) = let
			cL = compare l2 $ length cyc1 ; l2 = length cyc2
			cC = compare class2 class1
			in if cL /= EQ then cL else if cC /= EQ then cC else compare cyc2 cyc1  
	listLengthDeg 0 0 = [[]]; listLengthDeg 0 _ = []
	listLengthDeg n d = concat [map (i:)$ listLengthDeg (n-1) deg| i<-[0..23],let deg = d-degK3 i, deg>=0]
	multiply cy = [((partC,helem co),fromIntegral z) | co<-combs,let z=cupSym co cmo orbA orbB,z/=0] where 
		pi = cyclesPermute n cy
		perC = compose perA pi
		sorC = sortBy ((.Set.size).flip compare.Set.size) $ map Set.fromList $ cycles perC
		partC = PartLambda $ map Set.size sorC
		helem = concat.map (sortBy (flip compare).map snd).groupBy ((.Set.size.fst).(==).Set.size.fst)  
		combs = map (zip sorC) $ listLengthDeg (length sorC) (degA+degB-2*(n-length sorC))
		orbB = zip (map Set.fromList cy) lb
		cmo = map Set.fromList $ commonOrbits perA pi
	sumUp = map(\g-> (fst $ head g,sum $ map snd g)).groupBy((.fst).(==).fst).sortBy((.fst).compare.fst) 	
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

-- Hilfsfunktion: Filtert Erzeugerkompositionen
subpart (PartLambda pl,l) a = PartLambda $ sb pl l where
	sb [] _ = []
	sb pl [] = sb pl [0,0..]
	sb (e:pl) (la:l) = if la == a then e: sb pl l else sb pl l


toInt q = if n ==1 then z else 7777777 where (z,n) =(numerator q, denominator q)
toIntStrict q = if n ==1 then z else error"not integral" where (z,n) =(numerator q, denominator q)

{-
writeSym3' n = writeFile ("GAP_Code/GAP_n="++show n++"_Sym3N.txt") s where
	h4 = hilbBase n 4
	h6 = hilbBase n 6
	h2 = hilbBase n 2
	h222 = [(i,j,k)| i<-h2, j<-h2, i<=j, k<-h2, j<=k]
	somme [] [] = []
	somme a [] = a
	somme [] b = b
	somme a@((aa,va):ra) b@((bb,vb):rb) | aa==bb = (aa,va+vb):somme ra rb
		| aa < bb = (aa,va):somme ra b
		| otherwise=(bb,vb):somme a rb
	mult alpha = map (\(a,v)->(a,alpha*v))
	csaSP = cupSAsp n 6
	cup3 (n,m,l) = foldr somme [] [mult c2 $ csaSP (l,p) | p<-h4, let c2=cup2 p n m, c2 /= 0]	
	cup2 = memo3 cupSA
	ic = memo2 integerCreation
	base3 (i,j,k) = [((n,m,l),x*y*z)|n<-h2,let x=ic n i,x/=0, m<-h2,let y=ic m j, y/=0, l<-h2, let z=ic l k, z/=0]
	icup3 ijk = foldr somme [] [mult xyz $ cup3 nml | (nml,xyz)<-base3 ijk ]
	line (i,j,k) = [toInt$sum [v*creationInteger r q|(q,v)<-icup3(i,j,k)]| r<-h6]
	s = "a := [\n" ++ concat(intersperse ",\n" [show $line ijk | ijk<-h222]) ++"\n];;\n"

-}
