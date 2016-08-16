module Harmonics where

import InfinitePolynomial
import Partitions
import Data.Ratio

laplace (InfPol f) = infPol [ (PartAlpha b, x*y)| (PartAlpha a , x ) <- f, (b,y) <- l a] where
	l [] = []
	l (t:a) = if t >= 2 then (t-2 : a,fromIntegral $ t*t-t) : r else r where
		r = [ (t:c,x) | (c,x) <- l a]

radSq dim =  InfPol [ (PartAlpha ( b i), 1) | i<- [1..dim]] where
	b i = [if j==i then 2 else 0 | j <-[1..dim]]

harmPr dim deg f = infPol$list$rec 0 1 f where
	n = fromIntegral deg; d = fromIntegral dim
	r = radSq dim
	rec j a f = if 2*j> n then 0 else 
		infPolScale a f + r * rec (j+1) (a/4/(j+1)/(2-n-d/2+j)) (laplace f) 

decomp dim (-1) f = []
decomp dim (-2) f = []
decomp dim deg f = harmPr dim deg f : decomp dim (deg-2) ff where
	ff = negate$ infPol$list$ rec 1 (1/4/(2-n-d/2)) (laplace f) 
	n = fromIntegral deg; d = fromIntegral dim
	r = radSq dim
	rec j a f = if 2*j> n then 0 else 
		infPolScale a f + r * rec (j+1) (a/4/(j+1)/(2-n-d/2+j)) (laplace f) 

demon l = [ foldr lcm 1 $ map (denominator.snd) t | InfPol t <- x] where
	x = decomp (length l) (sum l) $ x_ l

denorm l = map (norm. (^2)) $ decomp (length l) (sum l) $ x_ l where
	norm (InfPol t) = sum [a*n o| (o,a) <-t]
	n (PartAlpha r) = fromIntegral $ product [if odd i then 0 else product [1,3..i-1] | i<-r] 
