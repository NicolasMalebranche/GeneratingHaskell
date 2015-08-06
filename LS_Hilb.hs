{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module LS_Hilb
	where

import Data.List
import Data.MemoTrie
import LS_Frobenius
import Partitions

data VertexOperator k = P Int k | L Int k | Del | C k deriving (Show,Eq,Ord)
data DelOne k = P_1 k | D deriving (Eq,Ord,Show)

newtype State a k = Vak { unVak:: [([VertexOperator k],a)] }

weight (P n k) = -n
weight (L n k) = -n
weight Del = 0
weight (C k) = 0

degree (P n k) = gfa_deg k
degree (L n k) = gfa_deg k + gfa_d
degree Del = 2

degMod2 (P n k) = gfa_deg k `mod`2
degMod2 (L n k) = (gfa_deg k + gfa_d) `mod`2
degMod2 Del = 2
degMod2 (C k) = gfa_deg k `mod` 2


showOperatorList [] = "|0>"
showOperatorList (Del:r) = "D " ++ showOperatorList r
showOperatorList (P n k:r) = sh ++ showOperatorList r where
	sh = (if n<0 then "p_"++show(-n)else "p"++show n)++"("++show k++") "
showOperatorList (L n k:r) = sh ++ showOperatorList r where
	sh = (if n<0 then "L_"++show(-n)else "L"++show n)++"("++show k++") "
showOperatorList (C k:r) = show k++ "[*] " ++ showOperatorList r 

instance (Show a, Show k) => Show (State a k) where
	show (Vak []) = "0"
	show (Vak [(l,x)]) = show x ++ " * \t"++showOperatorList l
	show (Vak ((l,x):r)) = show x ++ " * \t"++showOperatorList l ++ "\n"++show(Vak r) 



-- Operator product acting on Vacuum. Result is given in terms of deltas and P(-1) operators.
delState :: (GradedFrobeniusAlgebra k, Ord k) => [VertexOperator k] -> State Rational k

delState [] = Vak [([],1)] 
delState [Del] = Vak []
delState (Del : r) = Vak [(Del:o,x) | (o,x) <- unVak$ delState r]
delState (P (-1) k : r) = Vak [(P (-1) k:o,x) | (o,x) <- unVak$delState r]
delState ob@(P n k : r) = if n >= 0 then toDel $ nakaState ob  else 
	Vak $  scal z $ sparseNub [ (q++o, x*y) | (o,x) <- unVak $delState r, (q,y) <- replace] where
	replace =  ad (-1-n) (P (-1) k) 
	ad 0 p = [([p],1)]
	ad n p = sparseNub $ [ (q++o,x*y) | (o,x)<-adi, (q,y)<-komm ] ++ 
		[ (o++q,-x*y) | (o,x)<-adi, (q,y)<-komm ] where adi = ad (n-1) p 
	komm = sparseNub $ [ ([Del,P(-1) k],x) | (k,x) <- gfa_1]++ [ ([P(-1) k,Del],-x) | (k,x) <- gfa_1]
	z = recip $ fromIntegral $(-1)^(-1-n)* (product [1.. -1-n])
delState ob@(L _ _ :_) = toDel $ nakaState ob
delState (C k : r) =Vak$ sparseNub[ (q,x*y) | (o,x) <-unVak$ delState r, (q,y) <- commuteIn o] where
	commuteIn [] = [] -- see LiQinWang (5.6)
	commuteIn (Del: r) = [(Del:o,x) | (o,x) <- commuteIn r]
	commuteIn (p@(P (-1) k'):r)= sparseNub$ [(P(-1) k':o,commSign (C k) p x)| (o,x) <- commuteIn r] ++
		[ (o,x*y) | (q,x) <- gfa_mult k k', (o,y) <- unVak $ expAdDel (P(-1) q) r]

expAdDel p r = let
	maxpower = (gfa_d * sum (map weight r) - sum (map degree r) )`div` 2
	adDel l = sparseNub$ [ (Del:o,x)|(o,x) <- l] ++ [ (o++[Del],-x)|(o,x) <- l] 
	ads = [([p],1)] : map adDel ads
	facs = 1 : zipWith (*) [1..] facs
	exp = zipWith (scal.recip.fromIntegral) facs ads
	in Vak [(o++r,x) | (o,x) <- concat $ take (maxpower+1) exp]


-- Operator product acting on Vacuum. Result is given in terms of creation operators.
nakaState :: (GradedFrobeniusAlgebra k, Ord k) => [VertexOperator k] -> State Rational k

nakaState [] = Vak [([],1)]
nakaState [P n k] = Vak$ if n>=0 then [] else [([P n k],1)]
nakaState [L n k] = Vak$ sparseNub [(o,y*x/2) | 
	nu <- [n+1 .. -1], ((a,b),x) <- gfa_comult k, (o,y) <-unVak$nakaState $op nu a b ] where
	op nu a b = if nu < n-nu then [P nu a, P (n-nu) b] else [P (n-nu) a, P nu b]
nakaState [Del] = Vak []
nakaState [C k] = Vak []

nakaState (p@(P n k) : r)= Vak[(t,y*x) | (q,x) <- unVak$nakaState r, (t,y) <- pf q] where
	pf (p'@(P m k'): r) = if p<=p' then [(p:p':r,1)] else 
		[(p':o,commSign p p' x) | (o,x) <- unVak$nakaState (p:r)] ++ 
			if n+m==0 && x/=0 then [(r,x)] else [] where x=fromIntegral n * gfa_bilinear k k'

nakaState (l@(L n k) : r) = Vak$sparseNub [ (t,y*x) | (q,x) <-unVak$nakaState r, (t,y) <- lf q] where
	lf (p@(P m k'):r) = [ (o, commSign l p x) | (o,x) <- unVak$nakaState (p:l:r)] ++ 
		[ (o, fromIntegral(-m)*y*x) | (kk,x) <- gfa_mult k k', (o,y) <- unVak$nakaState$ P (n+m) kk : r]

nakaState (Del : r) = Vak$sparseNub [ (t,y*x) | (q,x) <- unVak$nakaState r, (t,y) <- df q] where
	df (p@(P n k):r) = sparseNub$ [ (o,x) | (o,x) <- unVak$nakaState (p:Del:r)] ++ 
		[ (o,fromIntegral n*x) | (o,x) <- unVak$nakaState (L n k : r)] ++
		scal bin [ (o,y*x) | (kk,x) <- ka , (o,y) <- unVak$nakaState (P n kk : r)] where
			bin = fromIntegral $ div (-n*(abs n - 1)) 2
			ka = sparseNub [ (kk, y*x) | (k',x) <- gfa_K, (kk,y) <- gfa_mult k' k]

nakaState (ob@(C _:r)) = toNaka $ delState ob

commSign p q = if odd $ degMod2 p * degMod2 q then negate else id

-- Transforms state representations
toDel (Vak l)  = Vak $ sparseNub[ (p,x*y)|(o,x) <- l, (p,y) <- unVak$delState o] 
toNaka (Vak l) = Vak $ sparseNub[ (p,x*y)|(o,x) <- l, (p,y) <- unVak$nakaState o] 
