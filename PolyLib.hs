module PolyLib where

-- Bibliothek fuer polynomielle Familien

import PowerSeries
import Polynomial
import Data.MemoTrie
import Elementary
import Data.Ratio


instance (Fractional a) => Fractional (Polynomial a) where
	fromRational = polyConst . fromRational
	recip = undefined

-- Allgemeine Routine zur Produktion othogonaler Polynome
-- a_n * p (n+1) = (b_n +x*c_n)*p n - d_n * p (n-1) 
orthogonalSequence a b c d n = mp n where
	mp = memo p
	p 0 = 1
	p n = let n1 = fromIntegral (n-1) 
		in if n<0 then 0 else fmap (/a n1) $
		fmap (*b n1) (mp (n-1)) + fmap (*c n1) (polyShift 1 $ mp (n-1)) - fmap (*d n1) (mp (n-2))

-- Pochhammer-Symbole
fallingFactorials :: Num a => [Polynomial a]
fallingFactorials = map (polyFromList.map fromInteger) $ scanl make [1] [1..] where
	make x n = zipWith (\ a b -> a-n*b) (0:x) (x++[0])

risingFactorials :: Num a => [Polynomial a]
risingFactorials = map (polyFromList.map fromInteger) $ scanl make [1] [1..] where
	make x n = zipWith (\ a b -> a+n*b) (0:x) (x++[0])
 

-- Tschebyscheff-Polynome
tcheb1 = zipWith (-) tcheb2 $ map (polyShift 1) $ 0:tcheb2
chebT n = memo t n where
	t 0 = 1
	t 1 = x
	t n = fmap(2*) (polyShift 1 (chebT (n-1))) - chebT (n-2) 

tcheb2 = 1 : (2*x) : zipWith op tcheb2 (tail tcheb2) where
	op a b = fmap (2*) (polyShift 1 b) - a
chebU n = memo u n where
	u 0 = 1
	u 1 = x+x
	u n = fmap(2*) (polyShift 1 (chebU (n-1))) - chebU (n-2) 

-- Hermite-Polynome
hermite = (!!) hermites where
	hermites = 1 : x : zipWith3 op [1..] hermites (tail hermites)
	op n a b = polyShift 1 b - fmap (*n) a
hermiteGenExp = seriesExpShift $ seriesGenerating [x,polyConst$ -1%2]

-- Shapiro-Polynome
shapiroP = 1 : zipWith3 op (map (2^) [0..]) shapiroP shapiroQ where
	op n p q = p + polyShift n q
shapiroQ = 1 : zipWith3 op (map (2^) [0..]) shapiroP shapiroQ where
	op n p q = p - polyShift n q

-- Jacobi-Polynome
jacobi a b = mj where
	mj = memo j
	j 0 = 1
	j 1 = Polynomial 1 $ Elem ( (a-b)/2 ) $ Elem ( (a+b)/2+1 ) 0 
	j n = fmap (/a1) $ fmap (*a2) (mj (n-1)) + polyShift 1 (fmap (*a3) $ mj (n-1)) - fmap (*a4) (mj (n-2)) where
		m = fromIntegral $ n-1
		a1 = 2*(m+1)*(m+a+b+1)*(2*m+a+b)
		a2 = (2*m+a+b+1)*(a^2-b^2)
		a3 = (2*m+a+b)*(2*m+a+b+1)*(2*m+a+b+2)
		a4 = 2*(m+a)*(m+b)*(2*m+a+b+2)

-- Gegenbauer-Polynome
gegenbauer a n = fmap (*s) $ jacobi (a-1/2) (a-1/2) n where
	s = rising (2*a) n / rising (a+1/2) n

-- Legendre Polynome
legendre n = jacobi 0 0 n

-- Laguerre Polynome
laguerre n = orthogonalSequence (+1) (\n -> 2*n+1) (const (-1)) id n
laguerreGen = seriesGeo * seriesExpShift ( seriesGenerating $ repeat (-x) )
	:: PowerSeries (Polynomial Rational) 

