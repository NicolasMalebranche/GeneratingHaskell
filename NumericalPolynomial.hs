{-# LANGUAGE MultiParamTypeClasses, DeriveFunctor, FlexibleInstances, ParallelListComp #-}
module NumericalPolynomial where

import qualified Polynomial as Po
import Partitions
import Data.MemoTrie
import Debug.Trace

-- Numerische Polynome sind solche, die ausgewertet an ganzen Zahlen
-- wieder ganze Zahlen ergeben
-- Das Nullpolynom hat negativen Grad
data NumericalPolynomial a = NumPoly {deg::a, eval::a->a} 

-- Baut numerisches Polynom aus normalem Polynom
nupoFromPoly p = NumPoly (fromInteger $ Po.deg p) (Po.polyEval p)

-- Rekonstruiert ein Polynom aus einer gegebenen Anfangssequenz von Werten
-- (beginnend mit eval 0)
nupoFromSequence :: Integral a => [a] ->  NumericalPolynomial a
nupoFromSequence l = NumPoly {deg=fromIntegral $ length dl - 1, eval= ev} where
	diffs _ [] = []
	diffs nls x@(0:y) = diffs (nls+1) $ zipWith (-) y x
	diffs nls x@(h:y) = h : replicate nls 0 ++ (diffs 0 $ zipWith (-) y x)
	dl = diffs 0 l
	ev n = sum $  [a*binomial n k | a<-dl | k<-if n<0 then [0..]else [0..n]] 
	

-- Vorwaerts-Differenzenoperator: p (n+1) - p n
nupoDiffFor p = NumPoly{deg=deg p-1, eval= \n-> eval p (n+1)-eval p n}

-- Rueckwaerts-Differenzenoperator: p (n+1) - p n
nupoDiffRear p = NumPoly{deg=deg p-1, eval= \n-> eval p n - eval p (n-1)}

-- Verschiebt das Argument
nupoShift a p =  NumPoly{ deg = deg p, eval=eval p.(+ negate a)}

-- Analog zur Taylorentwicklung um den Punkt a
-- p n = sum [c_i*choose (n-a) i | i<-[0..]]
nupoFallingTaylor a p = expand (deg p) vals where
	vals = map (eval p) [a..]
	expand d vals@(s:v) = if d<0 then [] else
		s : expand (d-1) (zipWith (-) v vals)

-- Analog zur Taylorentwicklung um den Punkt a
-- p n = sum [c_i*choose (n-a+i) i | i<-[0..]]
nupoRisingTaylor a p = expand (deg p) vals where
	vals = map (eval p) [a-1,a-2..]
	expand d vals@(s:v) = if d<0 then [] else
		s : expand (d-1) (zipWith (-) vals v)

binomial n kk = fromIntegral $ p 1 1 where
	p a i = if i>kk then a else p ((a*(n-kk+i))`div` i) (i+1)

-- siehe Definition
nupoFromGaps l = NumPoly {deg = fromIntegral $ length l-1, eval = s} where
	s t = sum [binomial (t+a) i -binomial t i | i<-[1..] | a <-l]

-- Stellt Polynom als Summe von Differenzen von Binomialkoeffizienten dar
nupoGaps p = reverse $ march $ reverse $ nupoFallingTaylor 0 p where
	march [] = []
	march (a:r) = a:march (zipWith (-) r $ map (binomial a) [2..] ) 


instance (Integral a, Show a) => Show (NumericalPolynomial a) where
	show p = "NuPo"++ show [eval p i | i<-[0..deg p]]
instance (Integral a) => Eq (NumericalPolynomial a) where
	p == q = all id $ map (\i->eval p i == eval q i) [0..max(deg p)(deg q)]
instance (Integral a) => Num (NumericalPolynomial a) where
	p + q = NumPoly{deg = max (deg p) (deg q), eval = \n-> eval p n + eval q n}
	p - q = NumPoly{deg = max (deg p) (deg q), eval = \n-> eval p n - eval q n}
	p * q = NumPoly{deg = deg p + deg q, eval = \n-> eval p n * eval q n}
	abs p = NumPoly{deg = deg p, eval = abs.eval p}
	signum p = NumPoly{deg = deg p, eval = signum.eval p}
	fromInteger i = NumPoly{deg = if i==0 then -1 else 0, eval = const $ fromInteger i}



