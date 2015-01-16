{-# LANGUAGE TypeOperators, TypeFamilies, ParallelListComp #-}

module SymmetricFunctions where

import Data.List 
import Data.MemoTrie
import Data.Ratio
import Partitions
import LinearAlgebra
import MatrixAlgorithms
import PowerSeries

-- Kombinatorische Funktionen
choose n k = ch1 n k where
	ch1 = memo2 ch
	ch 0 0 = 1
	ch n k = if n<0 || k<0 then 0 else if k> div n 2 + 1 then ch1 n (n-k) else
		ch1(n-1) k + ch1 (n-1) (k-1)

multinomial 0 [] = 1
multinomial n [] = 0
multinomial n (k:r) = choose n k * multinomial (n-k) r

kap a@(PartAlpha l) = mn `div` (product $map factorial l) * sum (zipWith (^) ll ll) where
	mn = multinomial (partWeight a) ll
	PartLambda ll = partAsLambda a

factorial 0 = 1
factorial n = n*factorial(n-1)

-- Wertet symmetrische Polynome aus
symEval vars = vl where
	es = seriesToList $ product [Elem 1 $ Elem x 0 | x<-vars]
	hs = seriesToList $ seriesInvShift hi where
		Elem _ hi = product [Elem 1 $ Elem (-x) 0 | x<-vars]
	ps = [sum $ map (^n) vars | n<-[0..]]
	[ef,hf,pf] = map (memo.(!!)) [es,hs,ps]
	prod f (PartLambda l) = product [f x |x<-l]
	vl 'e' = prod ef
	vl 'h' = prod hf
	vl 'p' = prod pf
	vl 's' = \j -> sum [ prod hf (partAsLambda i) * kostkaInv i j 
		| i<-partOfWeight (partWeight j) ]
	vl 'm' = \i -> sum [ monomialComplete i j * prod hf (partAsLambda j) 
		| j<-partOfWeight (partWeight i) ]


-- http://www.mat.univie.ac.at/~slc/wpapers/s68vortrag/ALCoursSf2.pdf , S. 48
-- Skalarprodukt monomiale Funktionen mit Potenzsummen
monomialScalarPower moI poI = (s * partZ poI) `div` quo where
	mI = partAsAlpha moI
	s = sum[a* moebius b | (a,b)<-finerPart mI (partAsLambda poI)]
	quo = product[factorial i| let PartAlpha l =mI, i<-l] 
	-- Alle Anordnungen vom Gewicht n, welche unters Profil passen
	nUnder 0 [] = [[]]
	nUnder n [] = [] 
	nUnder n (r:profile) = concat[map (i:) $ nUnder (n-i) profile | i<-[0..min n r]]
	-- Aufteilung von a auf l (mit Vielfachheiten)
	finerPart (PartAlpha a) (PartLambda l) = nub [(a`div` sym sb,sb) | (a,b)<-fp 1 a l, let sb = sort b] where
		sym = s 0 []
		s n acc [] = factorial n
		s n acc (a:o) = if a==acc then s (n+1) acc o else factorial n * s 1 a o
		fp i [] l = if all (==0) l then [(1,[[]|x<-l])] else []
		fp i (0:ar) l = fp (i+1) ar l
		fp i (m:ar) l = [(v*multinomial m p,addprof p op) 
			| p <- nUnder m (map (flip div i) l), 
			(v,op) <- fp (i+1) ar (zipWith (\j mm -> j-mm*i) l p)] where
				addprof = zipWith (\mm l -> replicate mm i ++ l)
	moebius l = product [(-1)^c * factorial c | m<-l, let c = length m - 1]


-- Basiswechselmatrix von Monomen nach Potenzsummen
-- !! Achtung !! keine ganzzahligen Koeffizienten
-- m_j = sum [ p_i * powerMonomial i j | i<-partitions]
powerMonomial :: (Partition a, Partition b) => a->b->Ratio Int
powerMonomial poI moI = monomialScalarPower moI poI % partZ poI

-- Basiswechselmatrix von Potenzsummen nach Monomen
-- p_j = sum [m_i * monomialPower i j | i<-partitions]
monomialPower :: (Partition a, Partition b, Num i) => a->b->i 
monomialPower lambda mu = fromIntegral $ numerator $ 
	memoizedMonomialPower (partAsLambda lambda) (partAsLambda mu)  
memoizedMonomialPower = memo2 mmp1 where
	mmp1 l m  = if partWeight l == partWeight m then mmp2 (partWeight m) l m else 0 
	mmp2 w l m = invertLowerDiag (map partAsLambda $ partOfWeight w) powerMonomial l m

-- Kostka Zahlen, untere Dreiecksmatrix mit Einsern auf der Diagonale
-- s_i = sum [ kostka i j * m_j | j<-partitions]
-- h_j = sum [ s_i * kostka i j | i<-partitions]
kostka :: (Partition a, Partition b, Num i) => a->b->i 
kostka lambda mu = fromIntegral $ memoizedKostka (partAsLambda lambda) (partAsLambda mu)  
memoizedKostka :: PartitionLambda Int -> PartitionLambda Int -> Int
memoizedKostka = memo2 b where
	b (PartLambda l) (PartLambda m) = build l (m,[0,0..])
	build [] (m,_) = if all (==0) m then 1 else 0
	build (r:l) (m,rest) = sum $ map (build l) $ fillLine r 1 m rest 
	fillLine 0 val m _ = [(m,[])] 
	fillLine n val [] _ = []
	fillLine n val (i:m) (j:rest) = [(i:newm,newrest) |(newm, newrest) <- fillLine n (val+1) m (j:rest)] ++ 
		if i>0 && val > j then [(newm,val:newrest) |(newm, newrest) <- fillLine (n-1) val ((i-1):m) rest] else []

-- Inverse der Matrix aus Kostkazahlen, 
-- untere Dreiecksmatrix mit Einsern auf der Diagonale
-- m_i = sum [ kostkaInv i j * s_j | j<-partitions ]
-- s_j = sum [ h_i * kostkaInv i j | i<-partitions ]
kostkaInv :: (Partition a, Partition b, Num i) => a->b->i 
kostkaInv lambda mu = fromIntegral $ memoizedKostkaInv (partAsLambda lambda) (partAsLambda mu)  
memoizedKostkaInv :: PartitionLambda Int -> PartitionLambda Int -> Int
memoizedKostkaInv = memo2 ko1 where
	ko1 l m  = if partWeight l == partWeight m then ko2 (partWeight m) l m else 0 
	ko2 w l m = invertLowerDiag1 (map partAsLambda $ partOfWeight w) memoizedKostka l m

-- completeMonomial, symmetrische unimodulare Matrix
-- h_i = sum [ completeMonomial i j * m_j | j<-partitions ]
-- completeMonomial = flip kostka * kostka
-- Skalarprodukt: <h,h> = completeMonomial h h
completeMonomial :: (Partition a, Partition b, Num i) => a->b->i 
completeMonomial lambda mu = fromIntegral $ memoizedKostkaTKostka (partAsLambda lambda) (partAsLambda mu)  
memoizedKostkaTKostka :: PartitionLambda Int -> PartitionLambda Int -> Int
memoizedKostkaTKostka = memo2 ko1 where
	ko1 l m  = if partWeight l == partWeight m then ko2 (partWeight m) l m else 0 
	ko2 w = mM (map partAsLambda $ partOfWeight w) (flip memoizedKostka) memoizedKostka 

-- monomialComplete, symmetrische unimodulare Matrix
-- m_i = sum [ monomialComplete i j * h_j | j<-partitions ]
-- monomialComplete = kostkaInv * flip kostkaInv
-- Skalarprodukt: <m,m> = monomialComplete m m
monomialComplete :: (Partition a, Partition b, Num i) => a->b->i 
monomialComplete lambda mu = fromIntegral $ memoizedKostkaTKostkaInv (partAsLambda lambda) (partAsLambda mu)  
memoizedKostkaTKostkaInv :: PartitionLambda Int -> PartitionLambda Int -> Int
memoizedKostkaTKostkaInv = memo2 ko1 where
	ko1 l m  = if partWeight l == partWeight m then ko2 (partWeight m) l m else 0 
	ko2 w = mM (map partAsLambda $ partOfWeight w) memoizedKostkaInv (flip memoizedKostkaInv)

