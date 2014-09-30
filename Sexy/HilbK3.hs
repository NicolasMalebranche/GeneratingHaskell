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
import qualified Data.IntMap as IntMap
import qualified Data.Set as Set
import ShowMatrix
import SymmetricFunctions
import Data.Ratio

type AnBase = (PartitionLambda Int, [K3Domain])
type SnBase = [([Int],K3Domain)]

-- Aequivalent zu partZ, nur mit gefaerbten Partitionen
anZ :: AnBase -> Int
anZ (PartLambda l, k) = comp 1 (0,undefined) 0 $ zip l k where
	comp acc old m (e@(x,_):r) | e==old = comp (acc*x) old (m+1) r
		| otherwise = comp (acc*x*fac m) e 1 r
	comp acc _ m [] = fac m * acc
	fac n = if n==0 then 1 else n*fac(n-1)

-- (Partition,[Klasse]) geht auf ([[(Zykel,Klasse)]],Multiplizitaet)
-- gibt die symmetrisierte Interpretation in A{S_n} zurueck
toSn :: AnBase -> ([SnBase],Int)
toSn = makeSn where
	allPerms = memo p where p n = map (array (0,n-1). zip [0..]) (Data.List.permutations [0..n-1]) 	
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
		fdown = {- nubSparse-} [(zip t l,v*w*24^def)| (r,v) <- fup, (l,w)<-cupAdLSparse(length t) r ] 
		def = toIntStrict ((Set.size or + 2 - length sset12 - length t)%2)

-- Tensort Sparse Listen zusammen
tensor [] = [([],1)]
tensor (t:r) = [(y++x,w*v) |(x,v)<-tensor r, (y,w) <- t ]

-- Multipliziert zwei Paare (PartLambda Int,[K3Domain])
multAn :: AnBase -> AnBase -> [(AnBase,Int)]
multAn a = multb where
	(asl,m) = toSn a
	toAn sn =(PartLambda l, k) where (l,k)= unzip$ sortBy (flip compare)$ map (\(c,k)->(length c,k)) sn
	multb (pb,lb) = map ungroup$ groupBy ((.fst).(==).fst) $sort elems where
		ungroup g@((an,_):_) = (an, m*(sum $ map snd g) )
		bs = zip (cycles $ partPermute pb) lb
		elems = [(toAn cs,v) | as <- asl, (cs,v) <- multSn as bs]

intCrea :: AnBase -> [(AnBase,Ratio Int)]
intCrea = map makeAn. tensor. construct where
	memopM = memo pM
	pM pa = [(pl,v) | p@(PartLambda pl)<-map partAsLambda$ partOfWeight (partWeight pa), let v = powerMonomial p pa, v/=0]
	construct pl = onePart pl : xPart pl : [ [(zip l $ repeat a,v)| (l,v)<- memopM (subpart pl a)] |a<-[1..22]] 
	onePart pl = [(zip l$ repeat 0, 1%partZ p)] where p@(PartLambda l) = subpart pl 0
	xPart pl = [(zip l$ repeat 23, 1)] where (PartLambda l) = subpart pl 23
	makeAn (list,v) = ((PartLambda x,y),v) where (x,y) = unzip$ sortBy (flip compare) list 

creaInt :: AnBase -> [(AnBase, Int)]
creaInt = map makeAn. tensor. construct where
	memomP = memo mP
	mP pa = [(pl,v) | p@(PartLambda pl)<-map partAsLambda$ partOfWeight (partWeight pa), let v = monomialPower p pa, v/=0]
	construct pl = onePart pl : xPart pl : [ [(zip l $ repeat a,v)| (l,v)<- memomP (subpart pl a)] |a<-[1..22]] 
	onePart pl = [(zip l$ repeat 0, partZ p)] where p@(PartLambda l) = subpart pl 0
	xPart pl = [(zip l$ repeat 23, 1)] where (PartLambda l) = subpart pl 23
	makeAn (list,v) = ((PartLambda x,y),v) where (x,y) = unzip$ sortBy (flip compare) list 


-- Cup-Produkt in integraler Kohomologie
cupInt :: AnBase -> AnBase -> [(AnBase,Int)]
cupInt a b = [(s,toIntStrict z)| (s,z) <- y] where
	ia = intCrea a; ib = intCrea b
	x = sparseNub [(e,v*w*fromIntegral z) | (p,v) <- ia, let m = multAn p, (q,w) <- ib, (e,z)<- m q] 
	y = sparseNub [(s,v*fromIntegral w) | (e,v) <- x, (s,w) <- creaInt e]

-- Fasst multiple Vorkommen in einer Sparse-Liste zusammen
sparseNub = map (\g->(fst$head g, sum $map snd g)).groupBy ((.fst).(==).fst).sort

-- Produkt aller Klassen aus der Liste
cupIntList :: [AnBase] -> [(AnBase,Int)]
cupIntList = makeInt. ci . cL where
	cL [b] = intCrea b
	cL (b:r) = x where
		ib = intCrea b
		x = sparseNub [(e,v*w*fromIntegral z) | (p,v) <- cL r, let m = multAn p, (q,w) <- ib, (e,z)<-m q]
	makeInt l = [(e,toIntStrict z) | (e,z) <- l]
	ci l = sparseNub [(s,v*fromIntegral w) | (e,v) <- l, (s,w) <- creaInt e]

degHilbK3 (lam,a) = 2*partDegree lam + sum [degK3 i | i<- a]

-- Basis von Hilb^n(K3) vom Grad d 
hilbBase = memo2 hb where
	hb n d = sort $map ((\(a,b)->(PartLambda a,b)).unzip) $ hilbOperators n d  

-- Alle möglichen Kombinationen von Erzeugungsoperatoren von 
-- Gewicht n und Grad d
hilbOperators = memo2 hb where 
	hb 0 0 = [[]] --Leeres Operatorprodukt
	hb n d = if n<0 || odd d || d<0 then [] else 
		nub $ map (Data.List.sortBy (flip compare)) $ f n d
	f n d = [(nn,0):x | nn <-[1..n], x<-hilbOperators(n-nn)(d-2*nn+2)] ++
		[(nn,a):x | nn<-[1..n::Int], a <-[1..22], x<-hilbOperators(n-nn)(d-2*nn)] ++
		[(nn,23):x | nn <-[1..n], x<-hilbOperators(n-nn)(d-2*nn-2)] 

-- Verändert das Gewicht eines AnBase Indizes
newWeight n (PartLambda l, a) = pq n (l++repeat 1,a++repeat 0) ([],[]) where
	pq 0 (i:l,b:a) (accl,acca) = if i==1&&b==0 then 
		Just (PartLambda $reverse accl, reverse acca) else Nothing
	pq m (i:l,b:a) (accl,acca) = if i<=m then pq (m-i) (l,a) (i:accl,b:acca) else Nothing

-- Hilfsfunktion: Filtert Erzeugerkompositionen
subpart (PartLambda pl,l) a = PartLambda $ sb pl l where
	sb [] _ = []
	sb pl [] = sb pl [0,0..]
	sb (e:pl) (la:l) = if la == a then e: sb pl l else sb pl l

-- Wandelt ganze rationale Zahl in Int um
toInt q = if n ==1 then z else 7777777 where (z,n) =(numerator q, denominator q)
toIntStrict q = if n ==1 then z else error"not integral" where (z,n) =(numerator q, denominator q)


-- Schreibfunktionen, produzieren Dateien mit Multiplikationsmatrizen

write22 n = writeFile ("GAP_Code/GAP_n="++show n++"_22.txt")  m where
	m = "a:= [\n" ++ concat (intersperse",\n"[show$col x2 y2 |x2<-h2,y2<-h2,x2<=y2] ) ++"\n];;\n"
	h2 = hilbBase n 2
	col x2 y2 = dense (hilbBase n 4) $ cupInt x2 y2

write24 n = writeFile ("GAP_Code/GAP_n="++show n++"_24.txt")  m where
	m = "a:= [\n" ++ concat (intersperse",\n"[show$col y4 y2 |y4<-h4,y2<-h2] ) ++"\n];;\n"
	h2 = hilbBase n 2; h4 = hilbBase n 4
	col y4 y2 = dense (hilbBase n 6) $ cupInt y4 y2
	
write222 n = writeFile ("GAP_Code/GAP_n="++show n++"_Sym3.txt")  m where
	m = "a:= [\n" ++ concat (intersperse",\n"$ map (show.col) hSym) ++"\n];;\n"
	h2 = hilbBase n 2; hSym = [[x2,y2,z2]|x2<-h2,y2<-h2,x2<=y2,z2<-h2,y2<=z2]
	col = dense (hilbBase n 6). cupIntList


-- Macht aus einer Sparse-Liste eine Dense-Liste
dense (p:o) (q:r) = if p==fst q then  snd q : dense o r else 0: dense o (q:r)
dense o [] = zipWith const [0,0..] o
dense [] _ = error "Falsch sortiert"


