module Harmonics where

import InfinitePolynomial
import Partitions
import Data.Ratio
import PolyLib
import Polynomial

laplace (InfPol f) = infPol [ (PartAlpha b, x*y)| (PartAlpha a , x ) <- f, (b,y) <- l a] where
	l [] = []
	l (t:a) = if t >= 2 then (t-2 : a,fromIntegral $ t*(t-1)) : r else r where
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

-- Integriert die ersten d Koordinaten über eine Sphäre. Normiert so, daß 1 auf 1 integriert
integrate d (InfPol p) = infPol[ (PartAlpha (drop d a) , x*f a / vol)|  (PartAlpha a,x) <- p] where
	f a = 2*product [ if odd i then 0 else gamma (bet i) |i<-take d $ a++repeat 0] / (gamma $ sum $ map bet $ take d $a++repeat 0 )
	bet n = (fromIntegral n + 1 )/2
	gamma n = product [ n-1, n-2 .. 1]
	vol = 2/ gamma (fromIntegral d/2)

reproducing d n =  gegn   where
	geg =  polyToList $ fmap (* (fromIntegral n /lam +1)) $ gegenbauer lam n
	gegn = sum [infPolConst(geg!!(n-i))*scalar^(n-i)*norm2^(i`div` 2) | i<-[0,2..n]]
	lam = fromIntegral d/2 +1 ::Rational
	scalar = sum [x_ $ replicate i 0 ++[1]++replicate (d-1) 0 ++[1]++replicate (d-i-1) 0 | i<- [0..d-1]]
	norm2 = radSq d * InfPol[ (PartAlpha (replicate d 0++a),x) | let InfPol p = radSq d, (PartAlpha a,x) <-p]
	

