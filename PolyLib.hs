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
fallingFactorial 0 = 1
fallingFactorial n = polyShift 1 rn - fmap (* (fromIntegral $ n-1)) rn 
	where rn = fallingFactorial $ n-1
fallingFactorialGenExp = seriesPowerShift x 1

risingFactorial 0 = 1
risingFactorial n = polyShift 1 rn + fmap (* (fromIntegral $ n-1)) rn 
	where rn = risingFactorial $ n-1
risingFactorialGenExp = seriesPowerShift (-x) (-1)

-- Tschebyscheff-Polynome
chebT n = mt n where
	mt = memo t
	t 0 = 1
	t 1 = x
	t n = fmap(2*) (polyShift 1 (mt (n-1))) - mt (n-2) 
chebTGen = chebUGen - fmap (polyShift 1) (seriesShift 1 chebUGen) 

chebU n = mu n where
	mu = memo u
	u 0 = 1
	u 1 = x+x
	u n = fmap(2*) (polyShift 1 (mu (n-1))) - mu (n-2) 
chebUGen = seriesInvShift $ seriesGenerating [-2*x,1]

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
jacobiGen a b = let 
	r = seriesPowerShift (1/2) $ seriesGenerating [-2*x,1]
	ri = seriesPowerShift (-1/2) $ seriesGenerating [-2*x,1]
	rs = fmap (fmap (/2)) $ seriesShift (-1) r + 1
	in ri * seriesPowerShift (-a) (rs-1) * seriesPowerShift (-b) rs


-- Gegenbauer-Polynome
gegenbauer a n = fmap (*s) $ jacobi (a-1/2) (a-1/2) n where
	s = rising (2*a) n / rising (a+1/2) n
gegenbauerGen a = seriesPowerShift (-a) $ seriesGenerating [-2*x,1]

-- Legendre Polynome
legendre n = jacobi 0 0 n
legendreGen = gegenbauerGen (1/2) 

-- Laguerre Polynome
laguerre n = orthogonalSequence (+1) (\n -> 2*n+1) (const (-1)) id n
laguerreGen = seriesGeo * seriesExpShift ( seriesGenerating $ repeat (-x) )
	:: PowerSeries (Polynomial Rational) 

