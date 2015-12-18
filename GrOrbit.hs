{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module GrOrbit where

import Data.Set
import Data.Maybe
import Data.List

orbitOf x nbf = run start where
	start = singleton x
	run set = if set == newset then set else run newset where
		newset = unions [ Data.Set.map g set  |g<-nbf ]


g (0,0) = (0,0)
g (1,0) = (0,1)
g (0,1) = (1,1)
g (1,1) = (1,0)

i = id
n _ = (0,0)

add (x,y)(u,v) = ( mod (x+u) 2, mod (y+v) 2)

data Group = I | G | T | S | SInv deriving (Enum,Show)
type H2 a = (a,a,a,a,a,a)
type A2 = (Integer,Integer,Integer,Integer)

m2 (a,b,c,d,e,f) = (m a,m b,m c,m d,m e,m f) where m = flip mod 2

actH2 I h2 = h2
actH2 T (u1,v1,w1,w2,v2,u2) = m2(u2,-v1,-w2,-w1,-v2,u1)
actH2 G (u1,v1,w1,w2,v2,u2) = m2(u1,-w2,-v2,v1-w2,w1-v2,u2)
actH2 S (u1,v1,w1,w2,v2,u2) = m2(u1+w1-w2+u2,v1,w1+u2,w2-u2,v2,u2)
actH2 SInv (u1,v1,w1,w2,v2,u2) =m2 (u1-w1+w2-u2,v1,w1-u2,w2+u2,v2,u2)

actA2 I a2 = a2
actA2 T (a,b,c,d) = (c,d,a,b)
actA2 G (a,b,c,d) = (b, mod (a+b) 2, c,d)
actA2 S (a,b,c,d) = (mod(a+c)2,mod(b+d)2,c,d)
actA2 SInv (a,b,c,d) = actA2 S (a,b,c,d) 

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
		ns = unions [act g s | g <- [I, G, S]]

suborbit2 x = run (singleton x) where
	run s = if s==ns then s else run ns where
		ns = unions [act g s | g <- [I, T, S]]

test1 = (unions.Prelude.map singleton) [ (1,0,0,0), (1,1,0,0), (0,1,0,0) ]
test2 = (unions.Prelude.map singleton) [ (1,0,1,0), (1,0,0,1), (0,0,1,1)::A2 ]

points35 = toList $ orbit test1 `Data.Set.union` orbit test2

to35 pt = [ (+) 1 $ fromJust $ findIndex (x==) points35  | x<- pt]

permut gs = to35 $ Prelude.foldr act points35 gs

possibilites = p 7  where
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


	 

fillpossil [a,b,c,d,e,f,g] = [ l i | i<-[1..36]] where
	l 36 = g
	l i = sum [ y | (x,y) <- zip alphaIdentities [a,b,c,d,e,f], i `member`x]



alphaIdentities = Prelude.map fromList [[1,26,31,33],[2,4,6,21,24,25],[3,5,7,9,11,13,15,17,19,27,29,34],[8,10,12,22,28,30],[14,16,18,23,32,35],[20]]

betaIdentities = Prelude.map fromList

data Mat a = M a a a a
mats = [M i n n i, 
	M n i i n,
	M g n n i,
	M i i n i]

fm (M a b c d) [x,y] = [a x `add` b y, c x `add` d y]
fs = Prelude.map fm mats

toL [(a,b),(c,d)] = [a,b,c,d]
frL [a,b,c,d] = [(a,b),(c,d)]

to3 f  = Data.Set.map f

actionsOn2 = Prelude.map to3 fs 


--test2 = (unions.Prelude.map singleton) [ [(1,0),(1,0)], [(1,0),(0,1)], [(0,0),(1,1)]]
test3 = (unions.Prelude.map singleton) [ [(1,0),(1,1)], [(1,1),(1,0)], [(0,1),(0,1)]]
test4 = (unions.Prelude.map singleton) [ [(0,0),(1,1)], [(1,1),(0,0)], [(1,1),(1,1)]]
test5 = (unions.Prelude.map singleton) [ [(1,0),(0,0)], [(1,1),(0,0)], [(0,1),(0,0)]]
