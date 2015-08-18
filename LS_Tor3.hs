{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module LS_Tor3
	where

import LS_Frobenius
import LS_Hilb
import Data.Ratio

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
l 4 = 
	--[ [([Ch 0 a,Ch 0 b],1)] | a<-[5..10],b<-[a..10]] ++
	--[ [([Ch 0 a,Ch 0 b, Ch 0 c],1)] | a<-[1..4],b<-[a+1..4], c<-[5..10]] ++
	--[ [([Ch 1 a],1)] | a<-[5..10]] ++ [ [([Ch 0 a,Ch 1 0],1)] | a<-[5..10]] ++
	--[ [([Ch 1 a,Ch 0 b],1)] | a<-[1..4], b<-[1..4]] ++ 
	[ [([Ch 0 a,Ch 0 b],1)] | a<-[1..4],b<-[11..14],a+b/=15]  ++
	--[ [([Ch 0 a,Ch 0 (15-a)],1)] | a<-[1..4]] ++
	[ [([Ch 2 0],1)] , j 15] 


l 8 = 
	--[ [([Ch 0 a,Ch 0 b, Ch 0 15],1)] | a<-[10,9..5],b<-[a,a-1..5]] ++
	--[ [([Ch 0 a,Ch 0 b, Ch 0 c],1)] | a<-[14,13..11],b<-[a-1,a-2..11], c<-[10,9..5]] ++
	--[ [([Ch 1 a, Ch 0 15],1)] | a<-[10,9..5]] ++ [ [([Ch 0 a,Ch 1 0, Ch 0 15],1)] | a<-[10,9..5]]++
	--[ [([Ch 1 a,Ch 0 b],1)] | a<-[14,13..11], b<-[14,13..11]] ++
	[ [([Ch 0 a,Ch 0 b,Ch 2 0 ],1)] | a<-[14,13..11],b<-[4,3..1], a+b /= 15] ++
	--[ [([Ch 0 15,Ch 0 a,Ch 0 (15-a)],1),([Ch 2 0,Ch 0 15],1)] | a<-[4,3..1]] ++
	[ [([Ch 2 15],1)] , [([Ch 0 15,Ch 0 15],1)]]

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

d = [([Del],-1%1)]
j a = [([Ch 0 a],1%1)]

h a = [([Ch 1 a], 1%1)]

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
	
