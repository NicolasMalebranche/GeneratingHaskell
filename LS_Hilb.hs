{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module LS_Hilb
	where

import Data.List
import Data.MemoTrie
import LS_Frobenius
import Partitions

data VertexOperator k = P Int k | L Int k | Del | C k deriving (Show,Eq,Ord)
data DelOne k = P_1 k | D deriving (Eq,Ord,Show)

deldeg D = 2
deldeg (P_1 k) = gfa_deg k
delweight D = 0
delweight (P_1 _) = 1


delOne [] = [([],1)]
delOne (Del : r) = [(D:o,x) | (o,x) <- delOne r]
delOne (P (-1) k : r) = [(P_1 k:o,x) | (o,x) <- delOne r]
delOne (P 0 _:_) = []
delOne (P n k : r) = if n > 0 then undefined else 
	scal z $ sparseNub [ (q++o, x*y) | (o,x) <- delOne r, (q,y) <- replace] where
	replace =  ad (-1-n) (P_1 k) 
	ad 0 p = [([p],1)]
	ad n p = sparseNub $ [ (q++o,x*y) | (o,x)<-adi, (q,y)<-komm ] ++ 
		[ (o++q,-x*y) | (o,x)<-adi, (q,y)<-komm ] where adi = ad (n-1) p 
	komm = sparseNub $ [ ([D,P_1 k],x) | (k,x) <- gfa_1]++ [ ([P_1 k,D],-x) | (k,x) <- gfa_1]
	z = recip $ fromIntegral $(-1)^(-1-n)* (product [1.. -1-n])

delOne (C k : r) = sparseNub[ (q,x*y) | (o,x) <- delOne r, (q,y) <- commuteIn o] where
	commuteIn [] = [([],1)]
	commuteIn (D: r) = [(D:o,x) | (o,x) <- commuteIn r]
	commuteIn (P_1 k' : r) = [(P_1 k:o,if odd (gfa_deg k*gfa_deg k')then -x else x )| (o,x) <- commuteIn r] ++ 
		[ (o++r,x)| (o,x) <- ead ] where
			ead = foldr ss [] $ zip ads $ [0..maxn r `div` 2] 
			ss (ap,n) l = scal (recip $ fromIntegral $ product [1..n]) ap ++ l
			ads = [ ([P_1 q],x) | (q,x) <- gfa_mult k k'] : map ad ads 
			ad l = sparseNub $ [ (D:o,x)  |(o,x) <- l] ++ [(o++[D],-x) | (o,x) <- l]
	maxn r = gfa_d * sum (map delweight r) - sum (map deldeg r) 
	
	
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
onVak [L n k] = sparseNub [(o,y*x*fromRational(1/2)) | 
	nu <- [n+1 .. -1], ((a,b),x) <- gfa_comult k, (o,y) <-onVak $op nu a b ] where
	op nu a b = if nu < n-nu then [P nu a, P (n-nu) b] else [P (n-nu) a, P nu b]
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

expAdDelta cut p r = let
	a = memo2 aa
	aa 0 k = onVak (p:replicate k Del++r)
	aa n k = sparseNub[(q,y*x) | (o,x)<-su, (q,y) <- onVak o] where
		su =sparseNub $ [(Del:o, (-1)^i *x)| i<-[0..n-1], (o,x)<-a(n-i-1)(k+i)] ++ [(o,(-1)^n*x) | (o,x)<-a 0 (k+n)]
	in [ (o, x/fromIntegral (product [1..n])) | n<-[0..cut], (o,x) <- a n 0]