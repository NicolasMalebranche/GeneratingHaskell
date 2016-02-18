{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor #-}
module SmallMatrix where

-- unkomplizierte Implementierung von 2x2 Matrizen

newtype Matrix2 a = Mat2 (a,a,a,a) deriving (Eq,Ord,Functor)


instance (Show a) => Show (Matrix2 a) where
	show (Mat2 (a,b,c,d)) = 
		"("++show a++"  "++show b ++" | "++
		     show c++"  "++show d ++")"

instance (Num a) => Num (Matrix2 a) where
	Mat2 (a,b,c,d) + Mat2 (u,v,w,x) = Mat2 (a+u,b+v,c+w,d+x)
	Mat2 (a,b,c,d) - Mat2 (u,v,w,x) = Mat2 (a-u,b-v,c-w,d-x)
	Mat2 (a,b,c,d) * Mat2 (u,v,w,x) = 
		Mat2 (a*u+b*w, a*v+b*x, c*u+d*w, c*v+d*x)
	negate (Mat2 (a,b,c,d)) = Mat2 (negate a, negate b, negate c, negate d)
	abs (Mat2 (a,b,c,d)) = Mat2 (abs a, abs b, abs c, abs d)
	signum (Mat2 (a,b,c,d)) = Mat2 (signum a, signum b, signum c, signum d)
	fromInteger i = Mat2 (j,0,0,j) where j = fromInteger i

det (Mat2 (a,b,c,d)) = a*d - b*c
trace (Mat2 (a,b,c,d)) = a+c
adjugate (Mat2 (a,b,c,d)) = Mat2 (d, -b, -c, a)
mV (Mat2 (a,b,c,d)) (x,y) = (a*x + b*y, c*x + d*y) 

instance (Fractional a) => Fractional (Matrix2 a) where
	fromRational r = Mat2 (q,0,0,q) where q = fromRational r
	recip m@(Mat2 (a,b,c,d)) =  let i = recip $ det m
		in Mat2 (d*i, -b*i, -c*i, a*i) 
