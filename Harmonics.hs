module Harmonics where

import InfinitePolynomial
import Partitions
import Data.Ratio
import Data.Array
import Elementary
import LinearAlgebra
import MatrixAlgorithms
import Polynomial
import RationalRoot
import PrimeFactors

laplace p = laplaceN (-1) p

-- Teilweiser Laplace-Operator d_1^2 + ... + d_n^2
laplaceN n (InfPol f) = infPol [ (PartAlpha b, x*y)| (PartAlpha a , x ) <- f, (b,y) <- l n a] where
	l n [] = []
	l 0 r = []
	l n (t:a) = if t >= 2 then (t-2 : a,fromIntegral $ t*(t-1)) : r else r where
		r = [ (t:c,x) | (c,x) <- l (n-1) a]

-- Radius zum Quadrat
radSq dim =  InfPol [ (PartAlpha ( b i), 1) | i<- [1..dim]] where
	b i = [if j==i then 2 else 0 | j <-[1..dim]]

-- Multipliziert so oft mit radSq d, bis das Polynom homogen vom Grad n ist
homogenize d n (InfPol f) = sum [ infPolScale x (l n a) | (PartAlpha a , x ) <- f] where
	l n a = let diff = n - sum (take d a) in
		if even diff then x_ a * radSq d ^ div diff 2 else error "Grad passt nicht"

-- Projiziert auf den harmonischen Anteil von f, wobei f homogen vom Grad deg in dim Dimensionen ist
harmPr dim deg f = infPol$list$rec 0 1 f where
	n = fromIntegral deg; d = fromIntegral dim
	r = radSq dim
	rec j a f = if 2*j> n then 0 else 
		infPolScale a f + r * rec (j+1) (a/4/(j+1)/(2-n-d/2+j)) (laplaceN dim f) 

decomp dim (-1) f = []
decomp dim (-2) f = []
decomp dim deg f = harmPr dim deg f : decomp dim (deg-2) ff where
	ff = negate$ infPol$list$ rec 1 (1/4/(2-n-d/2)) (laplace f) 
	n = fromIntegral deg; d = fromIntegral dim
	r = radSq dim
	rec j a f = if 2*j> n then 0 else 
		infPolScale a f + r * rec (j+1) (a/4/(j+1)/(2-n-d/2+j)) (laplace f) 

decompR dim deg f = zipWith (*) rads $ decomp dim deg f where
	rads = 1 : map (* radSq dim) rads

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

-- Skalarprodukt: x_1*x_{d+1} + ... + x_d*x_{2d}
scalar d = sum [x_ $ replicate i 0 ++[1]++replicate (d-1) 0 ++[1]++replicate (d-i-1) 0 | i<- [0..d-1]]

-- Für f homogenes Polynom vom Grad n in d Variablen gilt:
-- integrate d (reproducing d n * f) == harmPr d n f 
reproducing d n = infPolScale (fromIntegral $ product [d,d+2..d+2*n-2]) hpkn where
	kn = infPolScale (1/factorial n) $ scalar d ^ n
	hpkn = harmPr d n kn

bilinears d n = [ polyClean$polyFromList$berkowitz [1..m] $rix $ reproducing d k | k <- [n,n-2..0]] where
	mon = monomials d n
	m = length mon
	rix r = listArray ((1,1),(m,m)) [infPolConstCoeff$ integrate d $ x * ry | y<- mon, 
			let ry = integrate d $ r*y, x<-mon]


bilVector b d n = zipWith b x x where
	x = decompR d n $ x_ [n]


bil0 (InfPol a) (InfPol b) = sum [bi (alphList$partAdd p q) * x * y | (p,x) <- a, (q,y) <- b ] where
	bi [] = 1
	bi (t:r) = if odd t then 0 else fromIntegral (product [t-1,t-3..1]) * bi r

bil1 (InfPol a) (InfPol b) = sum [bi (alphList p) * x * y | (p,x) <- a, (q,y) <- b, q==p ] where
	bi [] = 1
	bi (t:r) = fromIntegral (product [1..t]) * bi r


