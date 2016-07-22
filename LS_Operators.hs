{-# LANGUAGE GeneralizedNewtypeDeriving, ParallelListComp #-}
module LS_Operators
	where

import LS_Frobenius
import Partitions


data VertexOperator k = P Int k | L Int k | Del | Ch Int k | GV Int k | ChT Int | J Int Int k deriving (Show,Eq,Ord)

-- J Konventionen nach LQW
-- J 0 n a == P n a
-- J 1 n a == - L n a
-- J p 0 a = p! Ch (p-1) a falls a*K == 0


newtype State a k = Vak { unVak:: [([VertexOperator k],a)] }

weight (P n _) = -n
weight (L n _) = -n
weight Del = 0
weight (Ch _ _) = 0
weight (GV _ _) = 0
weight (ChT _) = 0
weight (J p m _) = m

degree (P n k) = gfa_deg k
degree (L n k) = gfa_deg k + gfa_d
degree Del = 2
degree (Ch n k) = gfa_deg k + 2*n
degree (GV n k) = gfa_deg k + 2*n
degree (ChT n) = 2*n
degree (J p m k) = gfa_deg k + p*gfa_d

data ActsOn = DelState | Both | NakaState deriving (Show,Eq)


actsOn (P _ _) = Both
actsOn Del = Both
actsOn (L _ _) = NakaState
actsOn (Ch _ _) = DelState
actsOn (GV _ _) = DelState
actsOn (ChT _) = DelState
actsOn (J _ _ _) = NakaState

actOnNakaVac p@(P n _) = Vak $ if n<0 then [([p],1)] else []
actOnNakaVac (L n k) = Vak $ sparseNub [(o,y*x/2) | 
	nu <- [n+1 .. -1], ((a,b),x) <- gfa_comult k, (o,y) <-unVak$nakaState $op nu a b ] where
	op nu a b = if n-nu > 0 then [P nu a, P (n-nu) b] else [P (n-nu) a, P nu b]
actOnNakaVac Del = Vak []
actOnNakaVac (J p n a) = toNaka $ Vak $ scal (fromIntegral $ fact p) $ first ++ second  where
	fact n = if n == 0 then 1 else n*fact(n-1)
	s (PartAlpha a) = sum [ i^2*m | (i,m) <- zip [1..] a]
	pFact (PartAlpha a) = fromIntegral $ product $ map fact a
	creation al b =  [ (qL (partAsLambda al) ai, x*(-1)^(partLength al +1)) | (ai,x) <- tau ] where
		tau = gfa_comultN (partLength al - 1) b
		qL (PartLambda l) aa = [ P (-i) ai | (i,ai) <- zip l aa]
	first = [ (o,-x/pFact al) | al <- partOfWeightLength (-n) (p+1), (o,x) <- creation al a]
	second =[ (o,-x*y*fromIntegral (s al +n^2-2)/24/pFact al) | al <- partOfWeightLength (-n) (p-1), 
		(b,y) <- gfa_euler_mult a, (o,x) <- creation al b]

actOnDelVac p@(P n k) = Vak $ if n >= 0 then [] else scal ( 1/ fac) $ rec n where
	fac = fromIntegral $ product [n+1 .. -1] 
	rec (-1) = [([P(-1) k],1)]
	rec n = sparseNub [ t | (o,x) <- rec (n+1), (oo,y) <- p', t<-[(oo++o,x*y),(o++oo,-x*y)]]   
	p' = [ ([Del,P(-1) a], x) | (a,x) <-gfa_1 ] ++ [ ([P(-1) a,Del], -x) | (a,x) <-gfa_1 ] 
actOnDelVac Del = Vak  []
actOnDelVac (Ch _ _) = Vak  []
actOnDelVac (GV _ _) = Vak  []
actOnDelVac (ChT _) = Vak []

actOnJVac j@(J p n a) = if n>=0 || p > -n+1 || p> -n-1 && length (gfa_euler_mult a) ==0 then Vak [] else
	Vak [([j],1)]
actOnJVac (P n a) = if n<0 then Vak [([J 0 n a],-1)] else Vak []
actOnJVac (L n a) = if n< -1 then Vak [([J 1 n a],1)] else Vak []
actOnJVac _ = Vak []
 

-- ad(Del)^n(op)/n!
facDiff n op = let 
	bins 0 = [1]
	bins n = zipWith (-) (b++[0]) (0:b) where b = bins (n-1)
	ders = scanr (:) [] $ replicate (fromIntegral n) Del
	dels = scanl (flip (:)) [] $ replicate (fromIntegral n) Del
	fac = product [1..fromIntegral n] 
	in [ (d1++[op]++d2,fromIntegral b/fac) | d1<-ders | d2 <- dels | b <- bins n]

ad n u v = let
	rec = ad (n-1) u v
	--com = [ ([Del,P(-1) 0],1) , ([P(-1) 0,Del], -1)]
	new = [ z | (x,a) <- rec, (y,b) <- u, z <- [(x++y,-a*b),(y++x,a*b)]]
	in if n==0 then v else sparseNub new

commutator (P n a) (P m b) = if n+m==0 then [ ([], gfa_bilinear a b*fromIntegral n) ] else []
commutator Del (P n a) = ([L n a], fromIntegral n) : 
	[ ([P n c],x*y*sc) | (b,x) <- gfa_K, (c,y) <- gfa_mult b a] where
	sc = fromIntegral $ (-n*(abs n - 1) ) `div` 2
commutator p@(P _ _) Del = scal (-1) $ commutator Del p
commutator (L n a) (P m b) = [ ([P (n+m) c], x*fromIntegral(-m)) | (c,x) <- gfa_mult a b ]
commutator (Ch _ _) Del = []
commutator (Ch n a) (P (-1) y) = [ (c,x*fromRational z) | (b,x) <- gfa_mult a y, (c,z) <- facDiff n (P (-1) b) ]
commutator (GV _ _) Del = []
commutator (GV n a) (P (-1) y) = if odd n then [(s,negate x) | (s,x) <-csn] else csn where
	csn = commutator (Ch n a) (P (-1) y) 
commutator (ChT _) Del = []
commutator (ChT n) p@(P (-1) y) =  sparseNub $ first ++ second ++ third ++ fourth ++ fifth where
	k2= [(c,2*x*xx*z) | (a,x) <-gfa_K, (b,xx) <-gfa_K, (c,z) <- gfa_mult a b]
	todd_Inv_y = [[(y,1)], [(b,x*xx/2) | (a,x)<-gfa_K, (b,xx) <- gfa_mult a y],  
		sparseNub [(b,x*xx) | (a,x)<-scal (1/6) k2 ++ scal (1/12) gfa_euler, (b,xx) <- gfa_mult a y]]
	exp_K_y = [[(y,1)], [ (b,-x*xx) | (a,x) <- gfa_K, (b,xx) <- gfa_mult a y] ,
		[ (b,x*xx/2)| (a,x) <-k2, (b,xx) <- gfa_mult a y ] ]
	expTodd_y = zipWith scal [1,-1,1] todd_Inv_y
	first = [ (c,x) | (c,x) <-facDiff n p ]
	second = [ ( o++[GV gn b2], x*xx*z) | k <- [0..2] , (a,x) <- todd_Inv_y!!k, ((b1,b2),xx) <- gfa_comult a, 
		nu <- [0..n-k-2], let gn = n-nu-k-2, (o,z) <- facDiff nu (P (-1) b1) ]
	third = [ (c,x*xx*(-1)^nu) | nu<-[max (n-2) 0..n], 
		(a,x) <- exp_K_y !! (n-nu), (c,xx) <-facDiff nu (P (-1) a) ]
	fourth = [ ( o++[Ch gn b2], x*xx*z*(-1)^nu) | k <- [0..2] , (a,x) <- expTodd_y!!k, ((b1,b2),xx) <- gfa_comult a, 
		nu <- [0..n-k-2], let gn = n-nu-k-2, (o,z) <- facDiff nu (P (-1) b1) ]
	fifth = if n==2 then [ ([P(-1) b], x*xx) | (a,x) <- gfa_euler, (b,xx) <- gfa_mult a y] else []
-- experimental: J Operatoren. Funktionieren nur im Fall gfa_K == 0.
commutator (ChT _) (J _ 0 _) = []
{-
commutator (ChT n) (J 0 (-1) y) = sparseNub $ first ++ second ++ third ++ fourth ++ fifth where
	todd_Inv_y = [[(y,1)], [],  
		sparseNub [(b,xx/12) |  (b,xx) <- gfa_euler_mult y]]
	exp_K_y = [[(y,1)], [ ] ,[ ] ]
	expTodd_y = todd_Inv_y
	fact = fromIntegral.f where f n = if n ==0 then 1 else n*f(n-1)
	first = [ ([J n (-1) y] ,1/fact n) ]
	second = [ ( [J nu (-1) b1 , J (gn+1) 0 b2], x*xx*(-1)^(gn)/fact nu/fact(gn+1)) | k <- [0..2] , (a,x) <- todd_Inv_y!!k, ((b1,b2),xx) <- gfa_comult a, 
		nu <- [0..n-k-2], let gn = n-nu-k-2 ]
	third = [ ([J nu (-1) a],x*(-1)^nu/fact nu) | nu<-[max (n-2) 0..n], 
		(a,x) <- exp_K_y !! (n-nu) ]
	fourth = [ ( [J nu (-1) b1,J (gn+1) 0 b2], x*xx*(-1)^nu/fact(gn+1)/fact nu) | k <- [0..2] , (a,x) <- expTodd_y!!k, ((b1,b2),xx) <- gfa_comult a, 
		nu <- [0..n-k-2], let gn = n-nu-k-2 ]
	fifth = if n==2 then [ ([J 0 (-1) a], x) | (a,x) <- gfa_euler_mult y ] else []
-}
commutator (ChT n) (J 0 (-1) y) = if odd n then [] else first ++ second ++ third where
	fact = fromIntegral.f where f n = if n ==0 then 1 else n*f(n-1)
	first = [ ([J n (-1) y], 2/fact n) ]
	second = [ ([J nu (-1) b1, J (l+1) 0 b2], 2*x*(-1)^nu/fact (l+1)/fact nu ) | ((b1,b2),x) <-gfa_comult y, nu<-[0..n-2], let l= n-2-nu] 
		++[ ([J k (-1) b1, J (l+1) 0 b2], x*y*(-1)^k/fact (l+1)/fact k/6 ) | (ea,y) <- gfa_euler_mult y,((b1,b2),x) <-gfa_comult ea, k<-[0..n-4], let l= n-4-k]
	third = if n == 2 then [([J 0 (-1) ae], x) | (ae,x) <- gfa_euler_mult y] else []
commutator ch@(ChT _) (J p n a) = let
	rec = commutator ch (J 0 (n+1) a)
	one = scal (1/2) [(o,x*y*z) | (e1,z) <-gfa_1, (e2,y) <-gfa_1, (o,x) <-comRight ( comRight  (commutator ch (J 0 (-1) e1)) (J 2 0 e2) ) (J 0 (n+1) a) ]
	two = [(o,x*y) | (e,x) <- gfa_1, (o,y) <- comRight rec (J 1 (-1) e) ]
	comRight l o = [(s,x*y) | (r,x) <- l, (s,y) <- cr r ] where 
		cr [] = []
		cr [p] = commutator p o
		cr [p,q] = [(p:t,x) |(t,x) <-commutator q o] ++  [(t++[q],x) |(t,x) <-commutator p o]
	in if n>0 then undefined else if n==0 then [] else
	if p== 0 then scal (1/fromIntegral (n+1)) $ sparseNub$ one ++ two 
	else [ (o, x*xx/fromIntegral(n*p+n)) | (b,xx) <-gfa_1 , (o,x) <- comRight ( commutator ch (J 0 n a) ) (J (p+1) 0 b)]

commutator (J p m a) (J q n b) = first ++ second where
	mul =  gfa_mult a b
	qmpn 0 0 = if m+n==0 then fromIntegral m else 0
	qmpn p q = fromIntegral (q*m-p*n)	
	om = case (max p q, min p q) of 
		(2,0) -> if m+n==0 then fromIntegral (m-m^3)/6 else 0
		(1,1) -> if m+n==0 then fromIntegral (m-m^3)/12 else 0
		_ -> - fromIntegral omega / 12
	omega = p*(p-1)*(q*(n^3-n)+(p+3*q-2)*m*n^2) - q*(q-1)*(p*(m^3-m)+(q+3*p-2)*m^2*n)
	j p m a | p == -1, m==0 = [([],gfa_T a)]
		| p < -1 = []
		| otherwise = [([J p m a], 1)]
	first = [ (o, qmpn p q *x*t) | (ab,x) <-mul , (o,t) <- j (p+q-1) (m+n) ab ]
	second = [ (o,-x*y*t*om) | (ab,x) <- mul, (c,y) <- gfa_euler_mult ab, (o,t) <- j (p+q-3) (m+n) c]
commutator (J 0 m a) (P n b) = scal (-1) $ commutator (P m a) (P n b) 
commutator j@(J _ _ _) (P n a) = scal (-1) $ commutator j (J 0 n a)
commutator (P n a) j@(J _ _ _) = scal (-1) $ commutator (J 0 n a) j
commutator (L n a) j@(J _ _ _)  = scal (-1) $ commutator (J 1 n a) j
commutator Del j@(J p n a) = [ (o,x*y/2) | (b,x) <- gfa_1, (o,y)<- commutator (J 2 0 b) j]
commutator (Ch p a) j@(J _ _ _) = scal (1/fromIntegral (product [1..p+1])) $ commutator (J (p+1) 0 a) j 
		

showOperatorList [] = "|0>"
showOperatorList (Del:r) = "D " ++ showOperatorList r
showOperatorList (P n k:r) = sh ++ showOperatorList r where
	sh = (if n<0 then "p_"++show(-n)else "p"++show n)++"("++show k++") "
showOperatorList (L n k:r) = sh ++ showOperatorList r where
	sh = (if n<0 then "L_"++show(-n)else "L"++show n)++"("++show k++") "
showOperatorList (Ch n k:r) = "ch"++show n++"["++show k++ "] " ++ showOperatorList r 
showOperatorList (J p m k:r) = sh ++ showOperatorList r where
	sh = "J_"++show(p)++"_"++show m++"("++show k++") "

instance (Show a, Show k) => Show (State a k) where
	show (Vak []) = "0"
	show (Vak [(l,x)]) = show x ++ " * \t"++showOperatorList l
	show (Vak ((l,x):r)) = show x ++ " * \t"++showOperatorList l ++ " +\n"++show(Vak r) 



-- Operator product acting on Vacuum. Result is given in terms of deltas and P(-1) operators.
delState :: (GradedFrobeniusAlgebra k, Ord k) => [VertexOperator k] -> State Rational k

delState [] = Vak [([],1)] 
delState (o:r) = if actsOn o == NakaState then toDel $ nakaState (o:r) else result where
	result = Vak $ sparseNub[ (q,x*y) | (s,x) <-unVak$ delState r, (q,y) <- unVak $ commuteIn s]
	commuteIn [] = actOnDelVac o
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
	commuteIn [] = actOnNakaVac o
	commuteIn (p:r) = case (o,p) of
		(P _ _, P _ _) -> if o<p then Vak [(o:p:r,1)] else Vak cI 
		_ -> Vak cI
		where
		cI = case comm of [] -> ted; _ -> sparseNub $ ted ++ comm
		ted = [(n,x*sign*sign2) | (q,x) <- unVak $ commuteIn r, let (n,sign2)=nakaSort p q]
		comm =  [ (ds,x*y) | (q,x) <- commutator o p, (ds,y) <- unVak $ nakaState (q++r) ]
		sign= if odd (degree p) && odd (degree o) then -1 else 1

-- Operator product acting on Vacuum. Result is given in terms of J operators.
-- Assuming that the canonical bundle is trivial.
jState :: (GradedFrobeniusAlgebra k, Ord k) => [VertexOperator k] -> State Rational k
jState [] = Vak [([],1)]
jState (o:r) = result where
	result = Vak $ sparseNub[ (q,x*y) | (s,x) <- unVak $ jState r, (q,y) <- unVak $ commuteIn s]
	commuteIn [] = actOnJVac o
	commuteIn (pd:r) = case (o,pd) of
		(J p m a, J q n b) -> if (p+m,m-p,a)<(q+n,n-q,b) then Vak [(o:pd:r,1)] else Vak cI 
		_ -> Vak cI
		where
		cI = case comm of [] -> ted; _ -> sparseNub $ ted ++ comm
		ted = [(pd:q,x*sign) | (q,x) <- unVak $ commuteIn r]
		comm =  [ (ds,x*y) | (q,x) <- commutator o pd, (ds,y) <- unVak $ jState (q++r) ]
		sign= if odd (degree pd) && odd (degree o) then -1 else 1

-- Transforms state representations
toDel (Vak l)  = Vak $ sparseNub[ (p,x*y)|(o,x) <- l, (p,y) <- unVak$delState o] 
toNaka (Vak l) = Vak $ sparseNub[ (p,x*y)|(o,x) <- l, (p,y) <- unVak$nakaState o] 
toJ (Vak l) = Vak $ sparseNub[ (p,x*y)|(o,x) <- l, (p,y) <- unVak$jState o] 

scale a (Vak sta) = Vak $ scal a sta
add (Vak s) (Vak t) = Vak $ sparseNub $ s ++ t

multLists l stat = toNaka $ ml l stat where
	ml [] stat = stat
	ml (l:r) stat = let 
		Vak s = ml r stat
		ns = sparseNub[ (t,x*y*z) | (a,x) <- s, (o,y) <- l, (t,z)<- unVak $ delState (o++a) ]
		in Vak ns

-- Chern classes related to ChT
cT = (!!) c where
	c = [([],1::Rational)] : [if odd k then [] else cc k | k<-[1..] ]
	cc k = [ (ChT (2*i):o, x*fact(2*i)/fromIntegral(-k) ) | i<-[1..div k 2], (o,x) <- cT (k-2*i) ]
	fact n = fromIntegral $ product [1..n]

-- Unit element
one n = foldr add (Vak []) [scale (a*fac) $ nakaState [P(-1) k | _ <- [1..n]] | (k,a) <- gfa_1 ] where
	fac = recip $ fromIntegral $ product [1..n]


