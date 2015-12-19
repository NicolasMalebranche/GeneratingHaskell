{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, NoMonomorphismRestriction #-}

module GrOrbit where

import Data.Set 
import Data.Maybe
import Data.List


data Group = I | G | T | S | SInv | TGT deriving (Enum,Show)
type H2 a = (a,a,a,a,a,a)
type A2 = (Integer,Integer,Integer,Integer)

m2 (a,b,c,d,e,f) = (m a,m b,m c,m d,m e,m f) where m = flip mod 2

actH2 I h2 = h2
actH2 T (u1,v1,w1,w2,v2,u2) = m2(u2,-v1,-w2,-w1,-v2,u1)
actH2 G (u1,v1,w1,w2,v2,u2) = m2(u1,-w2,-v2,v1-w2,w1-v2,u2)
actH2 S (u1,v1,w1,w2,v2,u2) = m2(u1+w1-w2+u2,v1,w1+u2,w2-u2,v2,u2)
actH2 SInv (u1,v1,w1,w2,v2,u2) =m2 (u1-w1+w2-u2,v1,w1-u2,w2+u2,v2,u2)
actH2 TGT h2 = act T $ act G $ act T h2

actA2 I a2 = a2
actA2 T (a,b,c,d) = (c,d,a,b)
actA2 G (a,b,c,d) = (b, mod (a+b) 2, c,d)
actA2 S (a,b,c,d) = (mod(a+c)2,mod(b+d)2,c,d)
actA2 SInv (a,b,c,d) = actA2 S (a,b,c,d) 
actA2 TGT a2 = act T $ act G $ act T a2

u1 = (1,0,0,0,0,0) :: H2 Integer
v1 = (0,1,0,0,0,0) :: H2 Integer
w1 = (0,0,1,0,0,0) :: H2 Integer

class GroupAction x where
	act :: Group -> x -> x

instance (Integral a) => GroupAction (H2 a) where
	act = actH2
instance GroupAction A2 where
	act = actA2

instance GroupAction x => GroupAction [x] where
	act g = Prelude.map (act g)

instance (Ord x,GroupAction x) => GroupAction (Set x) where
	act g = Data.Set.map (act g)


orbit x = run (singleton x) where
	run s = if s==ns then s else run ns where
		ns = unions [act g s | g <- [I .. S]]

suborbit x = run (singleton x) where
	run s = if s==ns then s else run ns where
		ns = unions [act g s | g <- [I, G, S, TGT ]]

suborbit2 x = run (singleton x) where
	run s = if s==ns then s else run ns where
		ns = unions [act g s | g <- [I, T, S]]

test1 = (unions.Prelude.map singleton) [ (1,0,0,0), (1,1,0,0), (0,1,0,0)::A2  ]
test2 = (unions.Prelude.map singleton) [ (1,0,1,0), (1,0,0,1), (0,0,1,1)::A2 ]

points35 = toList $ orbit test1 `Data.Set.union` orbit test2

fI x =  (+) 1 $ fromJust $ findIndex (x==) points35  
to35 pt = [ fI x| x<- pt]

permut gs = to35 $ Prelude.foldr act points35 gs

possibilites = p 12  where
	p 0 = [[]]; p n = [ a:b | b<- p (n-1), a <- [0,1]]

checkposs p = let
	f = fillpossil p
	nq = [ f !! (i-1) | i <- permut [T]] ++[ f!!35]
	st = [ f !! (i-1) | i <- permut [T,S]] ++[ f!!35]
	gst = [ f !! (i-1) | i <- permut [T,S,G]] ++[ f!!35]
	ggst = [ f !! (i-1) | i <- permut [T,S,G,G]] ++[ f!!35]
	check2 = even$ sum $ zipWith (*) f nq
	checks = even$ sum $ zipWith (*) f f
	checkn = even$ sum $ zipWith (*) nq nq
	check3 = even$ sum $ zipWith(*) gst gst
	check4 = odd $sum $ zipWith (*) gst $zipWith (*) st $zipWith (*) f nq
	check5 = even $sum $ zipWith (*) ggst $ zipWith (*) f gst  
	check6 = even $sum $ zipWith (*) ggst $ zipWith (*) nq gst 
	check7 = even$ sum $ zipWith(*) st $ zipWith (*) nq ggst 
	in check2 && checks && checkn && check3 && check4 && check5 && check6 && check7

checkposs2 p = let 
	mul x y = sum $ zipWith (*) x y
	mul3 x y z= mul x $ zipWith (*) y z
	mul4 x y z t = mul3 x t $ zipWith (*) y z
	v1 = fillpossil p
	w2  = [ v1 !! (i-1) | i <- permut [G]] ++[ v1!!35]
	w1  = [ w2 !! (i-1) | i <- permut [T]] ++[ w2!!35]
	v2 =  [ w1 !! (i-1) | i <- permut [G]] ++[ w1!!35]
	u1w1= [ w1 !! (i-1) | i <- permut [S]] ++[ w1!!35]
	u2w2= [ u1w1 !! (i-1) | i <- permut [T]] ++[ u1w1!!35]
	check1 = even $ sum v1
	check2 = all even [mul y z | y<-[w1,w2,v2,u1w1,u2w2], z <-[w2,v2,u1w1,u2w2]]
	check3 = all even [mul3 v1 v2 w1, mul3 v1 u1w1 w1, mul3 v2 w1 u2w2]
	check4 = odd (mul4 w1 w2 v1 v2) && odd (mul4 u1w1 u2w2 w1 w2) && even (mul4 u1w1 v1 w1 v2)
	test = even (mul u1rep1 u1w1) && odd(mul4 u1rep1 u2w2 v1 v2)
	in check1 && check2 && check3 && check4 && test

v1poss = [fillpossil p | p<-possibilites, checkposs2 p] :: [[Integer]]
u1rep1 = [1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,0,0,0,0,0,1,1,0,1,0,1,0,1,1,0,0]
u1rep2 = [0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,1,1,1,1,0,0,1,0,1,0,1,0,0,1,1]

fillpossil t = [ l i | i<-[1..36]] where
	l 36 = last t
	l i = sum [ y | (x,y) <- zip betaIdentities  (init t) , i `member`x]


betaIdentities = Prelude.map fromList
	[[1,20,26],[2],[3,21,27],[4,5,8,9,22,24],[6,7,14,15,23,25],[10],[11,28,34],[12,13,16,17,30,32],[18],[19,29,35],[31,33]]
--	[[1,2,3,4,6,10,11,12,18,19,31],[20,21,5,7,28,13,29,33],[26,27,8,14,34,16,35],[9,15,17],[22,23,30],[24,25,32]]

alphaIdentities = Prelude.map fromList [[1,26,31,33],[20],[3,5,7,9,11,13,15,17,19,27,29,34],[2,4,6,21,24,25,8,10,12,22,28,30,14,16,18,23,32,35]]



