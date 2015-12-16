module GrOrbit where

import Data.Set
import Data.MemoTrie

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

data Mat a = M a a a a
mats = [M i n n i, 
	M n i i n,
	M g n n i,
	M i n n g,
	M i i n i,
	M i n i i,
	M i g n i,
	M i g n g,
	M i n g i,
	M i n g g,
	M g n i g]

fm (M a b c d) [x,y] = [a x `add` b y, c x `add` d y]
fs = Prelude.map fm mats

toL [(a,b),(c,d)] = [a,b,c,d]
frL [a,b,c,d] = [(a,b),(c,d)]

to3 f  = Data.Set.map f

actionsOn2 = Prelude.map to3 fs 


test1 = (unions.Prelude.map singleton) [ [(1,0),(0,0)], [(1,1),(0,0)], [(0,1),(0,0)]]
test2 = (unions.Prelude.map singleton) [ [(1,0),(1,0)], [(1,0),(0,1)], [(0,0),(1,1)]]
