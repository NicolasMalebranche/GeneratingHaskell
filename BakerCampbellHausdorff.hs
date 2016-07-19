module BakerCampbellHausdorff (bch)
	where

import Data.MemoTrie
import Data.List
import Data.Ord
import Data.Ratio

-- Implementiert die Baker-Campbell-Hausdorff Formel 
-- log (exp x * exp y)
bch comm x y = run 1 where
	highercomm = memo hc 
	hc [(0,1)] = [([y],1)]
	hc [(1,0)] = [([x],1)]
	hc ((0,0):r) = highercomm r
	hc ((0,n):r) = sparseNub [(q,a*b)| (o,a) <- highercomm $ (0,n-1):r, (q,b) <- comm y o]
	hc ((m,n):r) = sparseNub [(q,a*b)| (o,a) <- highercomm $ (m-1,n):r, (q,b) <- comm x o]
	fact n = if n==0 then 1 else n* fact (n-1)
	factor pp = a*b*c where
		a = 1 % product[fact s*fact r | (r,s) <-pp]
		b = 1 % sum [s+r | (r,s) <-pp]
		c = (-1)^(n+1) / fromIntegral n where n = length pp
	allOfWeight = memo aow :: Integer -> [[(Integer,Integer)]]
	aow 0 = [[]]
	aow n = [ p | k<-[1..n], r<-allOfWeight(n-k), i<-[0..k], let p=(i,k-i):r, length( highercomm p)>0]
	run n 	| length (allOfWeight n) == 0 = []
		| True = sparseNub [(o,t*f) | p <-allOfWeight n, let f = factor p, (o,t) <- highercomm p] : run (n+1)


sparseNub [] = []
sparseNub l = sn (head sl) (tail sl) where
	sl = sortBy (comparing fst) l
	sn (i,x) ((j,y):r) = if i==j then sn (i,x+y) r else app (i,x) $ sn (j,y) r
	sn ix [] = app ix []
	app (i,x) r = if x==0 then r else (i,x) : r
