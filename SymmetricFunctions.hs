{-# LANGUAGE TypeOperators, TypeFamilies, ParallelListComp #-}

module SymmetricFunctions where

import Data.List 
import Data.MemoTrie
import Partitions
import Data.Ratio

choose n k = ch1 n k where
	ch1 = memo2 ch
	ch 0 0 = 1
	ch n k = if n<0 || k<0 then 0 else if k> div n 2 + 1 then ch1 n (n-k) else
		ch1(n-1) k + ch1 (n-1) (k-1)

multinomial 0 [] = 1
multinomial n [] = 0
multinomial n (k:r) = choose n k * multinomial (n-k) r

factorial 0 = 1
factorial n = n*factorial(n-1)

-- Alle Anordnungen vom Gewicht n, welche unters Profil passen
nUnder 0 [] = [[]]
nUnder n [] = [] 
nUnder n (r:profile) = concat[map (i:) $ nUnder (n-i) profile | i<-[0..min n r]]

-- Aufteilung von a auf l (mit Vielfachheiten)
finerPart (PartAlpha a) (PartLambda l) = nub [(a`div` sym sb,sb) | (a,b)<-fp 1 a l, let sb = sort b] where
	sym = s 0 []
	s n acc [] = factorial n
	s n acc (a:o) = if a==acc then s (n+1) acc o else factorial n * s 1 a o
	fp i [] l = if all (==0) l then [(1,[[]|x<-l])] else []
	fp i (0:ar) l = fp (i+1) ar l
	fp i (m:ar) l = [(v*multinomial m p,addprof p op) 
		| p <- nUnder m (map (flip div i) l), 
		(v,op) <- fp (i+1) ar (zipWith (\j mm -> j-mm*i) l p)] where
			addprof = zipWith (\mm l -> replicate mm i ++ l)

moebius l = product [(-1)^c * factorial c | m<-l, let c = length m - 1]

-- http://www.mat.univie.ac.at/~slc/wpapers/s68vortrag/ALCoursSf2.pdf , S. 48
monomialScalarPower moI poI = (s * partZ poI) `div` quo where
	mI = partAsAlpha moI
	s = sum[a* moebius b | (a,b)<-finerPart mI (partAsLambda poI)]
	quo = product[factorial i| let PartAlpha l =mI, i<-l] 

pa = PartAlpha [3,3,1]
pl = PartLambda [4,3,2,1,1,1::Int]