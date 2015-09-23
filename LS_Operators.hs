{-# LANGUAGE GeneralizedNewtypeDeriving, ParallelListComp #-}
module LS_Operators
	where

import LS_Frobenius

data VertexOperator k = P Int k | L Int k | Del | S Int k | SV Int k | ChT Int deriving (Show,Eq,Ord)

newtype State a k = Vak { unVak:: [([VertexOperator k],a)] }

weight (P n _) = -n
weight (L n _) = -n
weight Del = 0
weight (S _ _) = 0
weight (SV _ _) = 0
weight (ChT _) = 0

degree (P n k) = gfa_deg k
degree (L n k) = gfa_deg k + gfa_d
degree Del = 2
degree (S n k) = gfa_deg k + 2*n
degree (SV n k) = gfa_deg k + 2*n
degree (ChT n) = 2*n


data ActsOn = DelState | Both | NakaState deriving (Show,Eq)

actsOn (P (-1) _) = Both
actsOn (P _ _) = NakaState
actsOn (L _ _) = NakaState
actsOn Del = Both
actsOn (S _ _) = DelState
actsOn (SV _ _) = DelState
actsOn (ChT _) = DelState


actOnVac p@(P n k) = Vak $ if n<0 then [([p],1)] else []
actOnVac (L n k) = Vak $ sparseNub [(o,y*x/2) | 
	nu <- [n+1 .. -1], ((a,b),x) <- gfa_comult k, (o,y) <-unVak$nakaState $op nu a b ] where
	op nu a b = if nu < n-nu then [P nu a, P (n-nu) b] else [P (n-nu) a, P nu b]
actOnVac Del = Vak  []
actOnVac (S _ _) = Vak  []
actOnVac (SV _ _) = Vak  []
actOnVac (ChT _) = Vak []

-- ad(Del)^n(op)/n!
facDiff n op = let 
	bins 0 = [1]
	bins n = zipWith (-) (b++[0]) (0:b) where b = bins (n-1)
	ders = scanr (:) [] $ replicate (fromIntegral n) Del
	dels = scanl (flip (:)) [] $ replicate (fromIntegral n) Del
	fac = product [1..fromIntegral n] 
	in [ (d1++[op]++d2,fromIntegral b/fac) | d1<-ders | d2 <- dels | b <- bins n]


commutator (P n a) (P m b) = if n+m==0 then [ ([], gfa_bilinear a b*fromIntegral n) ] else []
commutator Del (P n a) = ([L n a], fromIntegral n) : 
	[ ([P n c],x*y*sc) | (b,x) <- gfa_K, (c,y) <- gfa_mult b a] where
	sc = fromIntegral $ (-n*(abs n - 1) ) `div` 2
commutator (L n a) (P m b) = [ ([P (n+m) c], x*fromIntegral(-m)) | (c,x) <- gfa_mult a b ]
commutator (S _ _) Del = []
commutator (S n a) (P (-1) y) = [ (c,x*fromRational z) | (b,x) <- gfa_mult a y, (c,z) <- facDiff n (P (-1) b) ]
commutator (SV _ _) Del = []
commutator (SV n a) (P (-1) y) = if odd n then [(s,negate x) | (s,x) <-csn] else csn where
	csn = commutator (S n a) (P (-1) y) 
commutator (ChT _) Del = []
--commutator (ChT n) p@(P (-1) y) =  sparseNub $ first ++ second ++ fourth where
--	first = if odd n then [] else [ (c,2*x) | (c,x) <-facDiff n p ]
--	second = [ (c++[SV k b],-x*z) | ((a,b),x) <- gfa_comult y, k<- [0..n-2], (c,z) <-facDiff (n-k-2) (P (-1) a) ]
--	fourth = [ (c++[S k b],-x*z*fromIntegral ((-1)^(n-k))) | ((a,b),x) <- gfa_comult y, k<- [0..n-2], (c,z) <-facDiff (n-k-2) (P (-1) a) ]


showOperatorList [] = "|0>"
showOperatorList (Del:r) = "D " ++ showOperatorList r
showOperatorList (P n k:r) = sh ++ showOperatorList r where
	sh = (if n<0 then "p_"++show(-n)else "p"++show n)++"("++show k++") "
showOperatorList (L n k:r) = sh ++ showOperatorList r where
	sh = (if n<0 then "L_"++show(-n)else "L"++show n)++"("++show k++") "
showOperatorList (S n k:r) = "ch"++show n++"["++show k++ "] " ++ showOperatorList r 

instance (Show a, Show k) => Show (State a k) where
	show (Vak []) = "0"
	show (Vak [(l,x)]) = show x ++ " * \t"++showOperatorList l
	show (Vak ((l,x):r)) = show x ++ " * \t"++showOperatorList l ++ " +\n"++show(Vak r) 



-- Operator product acting on Vacuum. Result is given in terms of deltas and P(-1) operators.
delState :: (GradedFrobeniusAlgebra k, Ord k) => [VertexOperator k] -> State Rational k

delState [] = Vak [([],1)] 
delState (o:r) = if actsOn o == NakaState then toDel $ nakaState (o:r) else result where
	result = Vak $ sparseNub[ (q,x*y) | (s,x) <-unVak$ delState r, (q,y) <- unVak $ commuteIn s]
	commuteIn [] = actOnVac o
	commuteIn (pd:r) = case (o,pd) of 
		(Del,_) -> Vak [ (Del:pd:r,1) ]
		(P (-1) _, Del) -> Vak [ (o:pd:r,1) ]
		(P (-1) a, P (-1) b) -> if a <= b then Vak [(o:pd:r,1)] else Vak cI
		_ -> Vak cI
		where
		cI = case comm of [] -> ted; _ -> sparseNub $ ted ++ comm
		ted = [(pd:q,x*sign) | (q,x) <- unVak $ commuteIn r]
		comm =  [ (ds,x*y) | (q,x) <- commutator o pd, (ds,y) <- unVak $ delState (q++r) ]
		sign= if odd (degree pd) && odd (degree o) then -1 else 1


-- Operator product acting on Vacuum. Result is given in terms of creation operators.
nakaState :: (GradedFrobeniusAlgebra k, Ord k) => [VertexOperator k] -> State Rational k

nakaState [] = Vak [([],1)]
nakaState (o:r) = if actsOn o == DelState then toNaka $ delState (o:r) else result where
	result = Vak $ sparseNub[ (q,x*y) | (s,x) <- unVak $ nakaState r, (q,y) <- unVak $ commuteIn s]
	nakaSort p [] = ([p],1)
	nakaSort p (q:r) = case (odd (degree p)&& odd (degree q), compare p q) of
		(True,EQ) -> (p:q:r,0)
		(v, GT) -> (q:n, if v then -s else s) where (n,s) = nakaSort p r
		_ -> (p:q:r,1) 		
	commuteIn [] = actOnVac o
	commuteIn (p:r) = case (o,p) of
		(P _ _, P _ _) -> if o<=p then Vak [(o:p:r,1)] else Vak cI 
		_ -> Vak cI
		where
		cI = case comm of [] -> ted; _ -> sparseNub $ ted ++ comm
		ted = [(n,x*sign*sign2) | (q,x) <- unVak $ commuteIn r, let (n,sign2)=nakaSort p q]
		comm =  [ (ds,x*y) | (q,x) <- commutator o p, (ds,y) <- unVak $ nakaState (q++r) ]
		sign= if odd (degree p) && odd (degree o) then -1 else 1

-- Transforms state representations
toDel (Vak l)  = Vak $ sparseNub[ (p,x*y)|(o,x) <- l, (p,y) <- unVak$delState o] 
toNaka (Vak l) = Vak $ sparseNub[ (p,x*y)|(o,x) <- l, (p,y) <- unVak$nakaState o] 

scale a (Vak sta) = Vak $ scal a sta
add (Vak s) (Vak t) = Vak $ sparseNub $ s ++ t

multLists [] stat = stat
multLists (l:r) stat = let 
	Vak s = multLists r stat
	ns = sparseNub[ (t,x*y*z) | (a,x) <- s, (o,y) <- l, (t,z)<- unVak $ nakaState (o++a) ]
	in Vak ns
