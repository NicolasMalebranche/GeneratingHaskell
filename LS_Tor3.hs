{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module LS_Tor3
	where

import LS_Frobenius
import LS_Operators
import Data.Ratio
import Data.List

pairing a b = case multLists [a] b of 
	Vak [ ([P (-1) (Tor 15) ,P (-1) (Tor 15) ,P (-1) (Tor 15) ] , a) ] -> a
	_ -> 0

-- Multiplikationen mit Basen
l 0 = [scal (1/3)$j 0]
l 1 = map (j.Tor) [1..4]
l 2 = d : [ [([Ch 0 a,Ch 0 b],1%1)] | a<-[1..4],b<-[a+1..4]] ++ [ [([Ch 0 a],1%1)] | a<-[5..10]] 
l 3 = [ [([Ch 1 a],1)] | a<-[1..4]]++ [ [([Ch 0 a,Ch 1 0],1)] | a<-[1..4]]++
	[ [([Ch 0 a,Ch 0 b, Ch 0 c],1)] | a<-[1..4],b<-[a+1..4], c<-[b+1..4]] ++
	[ [([Ch 0 a,Ch 0 b],1)] | a<-[1..4],b<-[5..10]] ++
	[ [([Ch 0 a],1)] | a<-[11..14]] 
l 4 = [[([Ch 2 0],2)] ] ++
	[ [([Ch 0 a,Ch 0 b],1)] | a<-[5..10],b<-[a..10]] ++
	[ [([Ch 0 a,Ch 0 b, Ch 0 c],1)] | a<-[1..4],b<-[a+1..4], c<-[5..10]] ++
	[ [([Ch 1 a],1)] | a<-[5..10]] ++ [ [([Ch 0 a,Ch 1 0],1)] | a<-[5..10]] ++
	[ [([Ch 1 a,Ch 0 b],1)] | a<-[1..4], b<-[1..4]] ++ 
	[ [([Ch 0 a,Ch 0 b],1)] | a<-[1..4],b<-[11..14],a+b/=15]  ++
	[ [([Ch 0 a,Ch 0 (15-a)],1)] | a<-[1..4]] ++
	[  j 15] 


l 8 = [ [([Ch 2 15],2)] ] ++
	[ [([Ch 0 a,Ch 0 b, Ch 0 15],1)] | a<-[10,9..5],b<-[a,a-1..5]] ++
	[ [([Ch 0 a,Ch 0 b, Ch 0 c],1)] | a<-[14,13..11],b<-[a-1,a-2..11], c<-[10,9..5]] ++
	[ [([Ch 1 a, Ch 0 15],1)] | a<-[10,9..5]] ++ [ [([Ch 0 a,Ch 1 0, Ch 0 15],1)] | a<-[10,9..5]]++
	[ [([Ch 1 a,Ch 0 b],1)] | a<-[14,13..11], b<-[14,13..11]] ++
	[ [([Ch 0 a,Ch 0 b,Ch 2 0 ],1)] | a<-[14,13..11],b<-[4,3..1], a+b /= 15] ++
	[ [([Ch 0 15,Ch 0 a,Ch 0 (15-a)],1)] | a<-[1..4]] ++
	[ [([Ch 0 15,Ch 0 15],1)]]

l 10 = [([Ch 3 15],1%1)]  : [ [([Ch 0 a,Ch 0 b,Ch 0 15],1%1)] | a<-[14,13,12,11],b<-[a-1,a-2..11]] ++ 
	[ [([Ch 0 a,Ch 0 15,Ch 0 15],1%1)] | a<-[10,9..5]] 
l 11 = 	[ [([Ch 0 15,Ch 0 15,Ch 0 a],1)]| a<-[14,13,12,11]]	
l 12 = 	[ [([Ch 0 15,Ch 0 15,Ch 0 15],1)]]

-- rationale Basen
bas n = [multLists [m] one | m<- l n]

gramSchmidt [] [] = []
gramSchmidt (l:ls) (x:xs) = scal (recip $pairing or x) or : los where
	or = orth los xs
	los = gramSchmidt ls xs
	orth [] [] = l 
	orth (lo:lr) (x:xr) = sparseNub $ o ++ scal (-pairing o x/pairing lo x) lo where
		o = orth lr xr 

one = scale (1%6) $ nakaState $ replicate 3 $ P (-1) (Tor 0)

d = [([Ch 1 (Tor 0)],-1%1)]
j a = [([Ch 0 a],1%1)]

h a = [([Ch 1 a], 1%1)]

k a = [([Ch 2 a], 1%1)]

-- ist theta ^* d etwa durch 3 teilbar? -- nöö, q(delta ) = 6
-- theta^* d^4
th_del_4 = multLists [d,d,d,d] one `add`
	scale (-24) (multLists [j 1, j 2, j 3, j 4, j 15] one ) `add`
	scale (24) 	(multLists [j 1, j 2, j 13, j 14] one)`add`
	scale (-24)	(multLists [j 1, j 3, j 12, j 14] one)`add`
	scale (24)	(multLists [j 1, j 4, j 11, j 14] one)`add`
	scale (24)	(multLists [j 2, j 3, j 12, j 13] one)`add`
	scale (-24)	(multLists [j 2, j 4, j 11, j 13] one)`add`
	scale (24)	(multLists [j 3, j 4, j 11, j 12] one)`add`
	scale (120)	(multLists [j 1, j 14, j 15] one)`add`
	scale (-120)(multLists [j 2, j 13, j 15] one)`add`
	scale (120)	(multLists [j 3, j 12, j 15] one)`add`
	scale (-120)(multLists [j 4, j 11, j 15] one)

th_del_2 = multLists [d,d] one 	`add`
	multLists [j 1, j 14] one `add`
	multLists [j 13,j 2] one `add`
	multLists [j 3, j 12] one `add`
	multLists [j 11, j 4] one 

td2 = th_del_2 `add`  -- divisible by 3
	scale (-1) (multLists [j 5,j 10] one) `add`
	(multLists [j 6,j 9] one) `add`
	scale (-1) (multLists [j 7,j 8] one) 
	

th_del_3 = multLists [d,d,d] one `add` -- divisible by 4
	scale (4) (multLists [d, j 1,j 14] one) `add` 
	scale (-4) (multLists [d, j 2,j 13] one) `add` 
	scale (4) (multLists [d, j 3,j 12] one) `add` 
	scale (-4) (multLists [d, j 4,j 11] one) 

td3 = th_del_3 `add`  -- divisible by 12
	scale (-4) (multLists [d, j 5, j 10] one) `add` 
	scale (4) (multLists [d, j 6, j 9] one) `add` 
	scale (-4) (multLists [d, j 7, j 8] one)

-- second chern class of tautological sheaf = p_3(1)/3 *
c2 = scal (1%3) [([Ch 1 (Tor 0),Ch 1 (Tor 0)],1), 
	([Ch 0 1, Ch 0 14],1), ([Ch 0 13, Ch 0 2],1), ([Ch 0 3, Ch 0 12],1), ([Ch 0 11, Ch 0 4],1), 
	([Ch 0 5, Ch 0 10],-1), ([Ch 0 6, Ch 0 9],1), ([Ch 0 7, Ch 0 8],-1),
	([Ch 0 15],-3) ]
-- 12* c2^2 == d^4
-- 0 == multLists [c2,c2] one `add` scale (-1%12) (multLists [d,d,d,d] one)


bogo [Ch 0 (Tor 5)] [Ch 0 (Tor 10)] = 1
bogo [Ch 0 (Tor 6)] [Ch 0 (Tor 9)] = -1
bogo [Ch 0 (Tor 7)] [Ch 0 (Tor 8)] = 1
bogo [Ch 0 (Tor 8)] [Ch 0 (Tor 7)] = 1
bogo [Ch 0 (Tor 9)] [Ch 0 (Tor 6)] = -1
bogo [Ch 0 (Tor 10)] [Ch 0 (Tor 5)] = 1
bogo [Ch 1 (Tor 0)] [Ch 1 (Tor 0)] = 6
bogo _ _ = 0

bogoSym (a:b:c:d:r) = 3 * ( bogo [a] [b]*bogo [c] [d] + bogo [a] [c]*bogo [b] [d] + bogo [a] [d]*bogo [b] [c] )

sym4 = [(a++b++c++d,u*v*w*x)|i<- [0..6], j<-[i..6], k<-[j..6], m<-[k..6], let [(a,u)] = ll!!i, let [(b,v)]=ll!!j, let [(c,w)]= ll!!k, let [(d,x)]=ll!!m] where
	ll = d : [ [([Ch 0 a],1%1)] | a<-[5..10]] 

zer = [(a++b++c++d,u*v*w*x)|i<- [0..3], j<-[i+1..3], let [(a,u)] = l 1!!i, let [(b,v)]=l 1!!j, [(c,w)] <-l 2, [(d,x)]<-l 4] 


writeM = writeFile ("Matrix.txt") m where
	m = "a:= [\n" ++ concat (intersperse",\n"$ map (show.col) (sym4++zer)) ++"\n];;\n"
	col s = [p| t <- bs, let p=pairing [s] t ]
	bs = bas 4

writeV = writeFile ("Vector.txt") m where
	m = "b:= \n" ++show x ++"\n;;\n"
	x = [numerator $ i* bogoSym s | (s,i) <- sym4 ] ++ replicate 8034 0

writeM4 = writeFile "Matrix4.txt" m where
	m = "a:= [\n" ++ concat (intersperse",\n"$ map (show.col) kum4) ++"\n];;\n"
	col s = [if denominator p== 1 then numerator p else error"notInt"| t <- bs, let p=pairing s t ]
	bs = map (\x -> multLists [x] mayK) kum4
	
-- Basis auf der Kummerschen ?
kum4 = [ [([Ch 0 a,Ch 1 0],1/3)] | a<-[5..10]] ++
	[ [([Ch 0 a,Ch 0 a],1/2),([Ch 1 a],1)] | a<-[5..10]] ++
	[  j 15 ,  [([Ch 1 0,Ch 1 0],1/9)] , [([Ch 2 0],2/3)] ] ++
	[ [([Ch 0 a,Ch 0 b],1)]| a<-[5..10], b<-[a+1..10] ] ++
	[ [([Ch 0 5,Ch 0 10],1/6),([Ch 0 6,Ch 0 9],-1/6),([Ch 0 7,Ch 0 8],1/6)]  ]
{-[[([Ch 2 0],1/3)] ] ++
	[ [([Ch 0 a,Ch 0 b],1)] | a<-[5..10],b<-[a..10]] ++
	[ [([Ch 1 a],1)] | a<-[5..10]] ++ [ [([Ch 0 a,Ch 1 0],1)] | a<-[5..10]] ++
	[ [([Ch 1 a,Ch 0 b],1)] | a<-[1..4], b<-[1..4]] ++ 
	[  j 15 ,  [([Ch 1 0,Ch 1 0],1/3)] ]  
-}
-- Kohomologieklasse der verallgemeinerten Kummerschen
-- == multLists [j 1, j 2, j 3, j 4] one
mayK = scale (-1) (bas 4!!6) `add` 
	scale (1) (bas 4!!10) `add` 
	scale (-1) (bas 4!!13) `add` 
	scale (1) (bas 4!!27) `add` 
	scale (-1) (bas 4!!32) `add` 
	scale (1) (bas 4!!37) `add` 
	scale (1) (bas 4!!42) `add` 
	scale (-1) (bas 4!!47) `add` 
	scale (1) (bas 4!!52) `add` 
	scale (-2) (bas 4!!98) `add` 
	scale (2) (bas 4!!99) `add` 
	scale (-2) (bas 4!!100) `add` 
	scale (2) (bas 4!!101) `add` 
	scale (6) (bas 4!!102) 


-- Tangentialbündel
c2Tang = (scale (3%2) $ foldr add (Vak []) [ scale x $ nakaState (P (-1) 0: map (P (-1))r)  | (r,x) <- gfa_comultN 2 (Tor 0)]) `add` 
	(scale (-1%3) $ nakaState [P (-3) 0] )
-- = multLists [[([Ch 2 0],10),([Ch 1 0, Ch 1 0],-2) ]] one
-- =  [([Ch 0 5, Ch 0 10],4::Rational),([Ch 0 6, Ch 0 9],-4),([Ch 0 (Tor 7), Ch 0 8],4), ([Del,Del],-1/3)]
c4Tang = scale (4%3) $ foldr add (Vak []) [ scale x $ nakaState (map (P (-1))r)  | (r,x) <- gfa_comultN 3 (Tor 0)]

-- Hassett und Tschinkel Objekte
w = [ ([ChT 2],-3/8), ([Ch 1 (Tor 0),Ch 1 0],9%8)]
yp = [([ChT 2],-1%24), ([Ch 1 (Tor 0),Ch 1 0],1%72) ]

-- Ungerade ganzzahlige Basen der Kummerschen (8 Stueck jeweils)
bas3 = [ j $ Tor i | i <- [14,13..11]] ++ [ h i | i<-[1..4]]
bas5 = [ [([Ch 2 $Tor i],2/3)] | i<-[1..4]] ++ [ h i | i<-[14,13..11]]
writePairing = putStrLn $concat $  intersperse "\n" $  map f [0..7] where
	f i = show $ map (flip pairing $ multLists [bas3!!i] mayK) bas5


