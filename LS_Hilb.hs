{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module LS_Hilb
	where

import Data.List
import Data.MemoTrie
import LS_Frobenius
import Partitions

data VertexOperator k = P Int k | L Int k | Del | C k deriving (Show,Eq,Ord)


-- Grad eines Operators mod 2
opDeg (P _ k) = gfa_deg k
opDeg (L _ k) = gfa_deg k + gfa_d
opDeg Del = 2
opDeg (C k) = gfa_deg k -- in Wahrheit inhomogen

commSign p q = if odd $ opDeg p * opDeg q then negate else id


--onVak :: (Fractional a, Eq a, GradedFrobeniusAlgebra k, Ord k) => [VertexOperator k] -> [([VertexOperator k],a)]

asAnBase op = [((PartLambda$ f o, s o), x) | (o,x) <- onVak op] where
	f l = [ -n | P n _ <- l]
	s l = [ k  | P _ k <- l]

onVak [] = [([],1::Rational)]

onVak [P n k] = if n>=0 then [] else [([P n k],1)]
onVak [L n k] = [ (op nu a b,x*fromRational(1/2)) | nu <- [n+1 .. -1], ((a,b),x) <- gfa_comult k ] where
	op nu a b = sort $ if nu < n-nu then [P nu a, P (n-nu) b] else [P (n-nu) a, P nu b]
onVak [Del] = []
onVak [C k] = [([],1)]

onVak (p@(P n k) : r) = [ (t,y*x) | (q,x) <- onVak r, (t,y) <- pf q] where
	pf (p'@(P m k'): r) = if p<=p' then [(p:p':r,1)] else 
		[(p':o,commSign p p' x) | (o,x) <- onVak (p:r)] ++ 
			if n+m==0 && x/=0 then [(r,x)] else [] where x=fromIntegral n * gfa_bilinear k k'

onVak (l@(L n k) : r) = sparseNub [ (t,y*x) | (q,x) <- onVak r, (t,y) <- lf q] where
	lf (p@(P m k'):r) = [ (sort $ p:o, commSign p l x) | (o,x) <- onVak (l:r)] ++ 
		[ (o, fromIntegral(-m)*y*x) | (kk,x) <- gfa_mult k k', (o,y) <- onVak (P (n+m) kk : r)]

onVak (Del : r) = sparseNub [ (t,y*x) | (q,x) <- onVak r, (t,y) <- df q] where
	df (p@(P n k):r) = [ (sort $ p:o,x) | (o,x) <- onVak (Del:r)] ++ 
		[ (o,fromIntegral(n)*x) | (o,x) <- onVak (L n k : r)] ++
		scal bin [ (o,y*x) | (kk,x) <- ka , (o,y) <- onVak (P n kk : r)] where
			bin = fromIntegral $ div (-n*(abs n - 1)) 2
			ka = sparseNub [ (kk, y*x) | (k',x) <- gfa_K, (kk,y) <- gfa_mult k' k]

onVak (C a : r) = sparseNub [ (t,y*x) | (q,x) <- onVak r, (t,y) <- cf q] where
	cf (q@(p@(P n k):r)) = [ (sort $ p:o,x) | (o,x) <- onVak (C a:r)] ++ commutator where
		commutator =  []--if n == -1 then [ (o,x*y*z*f j)| j<- [0..maxpower], (ka,y)<-gfa_mult a k, (op,x) <- diff j (P (-1) ka), (o,z) <-onVak (op++r)] else[]
		f k = fromRational (1/factorial k)
		maxpower = sum [ -n*gfa_d - gfa_deg k | P n k <- q] `div` 2
		diff k op = [ (replicate (k-i) Del ++ [op] ++ replicate i Del, (-1)^i * binomial k i) | i<-[0..k]] 
	factorial n = product [1..n]
	binomial n k = foldl (\ b (m,i) -> div (b*m) i) 1 $ zip [n,n-1 ..] [1..k]







