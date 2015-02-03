{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor, UndecidableInstances, FlexibleInstances #-}
module MatrixAlgorithms where

import Data.MemoTrie
import Data.Array
import LinearAlgebra

-- Hilfsfunktionen für Lineare Algebra

-- Berechnet die Koeffizienten des charakteristischen
-- Polynoms mit dem Algorithmus von Berkowitz.
-- Die Determinante ist das letzte Listenelement.
-- vs sind die Indizes der quadratischen Matrix m
berkowitz vs m = let 
	c j = toep where
		ii = vs!!(j-1)
		toep i k | k>i = 0
			| k==i = 1
			| otherwise = rms ! (i-k-1)
		rms = listArray (0,n) [-vElem mr ii | mr <- mpowers]
		mpowers = scanl (vM $take (j-1) vs) (mRow m ii) (repeat m)
	p 0 = delta 0
	p j = mV [0..j+1] (c j) (p (j-1)) 
	n = length vs
	in map (p n) [0..n]

-- Berechnet die adjunkte Matrix und die Determinante mit
-- dem Berkowitz-Algorithmus. Die Inverse ist Adjunkte/Det.
adjugate vs m = (memo2 adj, det) where 
	det:char = reverse $ berkowitz vs m
	mpowers = m : map (mM vs m) mpowers
	adj i j = negate $ sum [c * mp i j | (c,mp) <- zip char (delta:mpowers)]

-- Invertiert untere Dreiecksmatrix
invertLowerDiag vs a = ild where
	ild = memo2 inv
	inv i j | i<j = 0
		| otherwise = (delta i j - sum [a i k * ild k j | k<-vs, i>k , k>= j]) / a i i

-- Invertiert untere Dreiecksmatrix, deren Diagonaleinträge gleich 1 sind
invertLowerDiag1 vs a = ild where
	ild = memo2 inv
	inv i k | i<k = 0
		| i==k = 1
		| otherwise = - sum [a i j * ild j k | j<-vs, i>j]

-- Invertiert obere Dreiecksmatrix, deren Diagonaleinträge gleich 1 sind
invertUpperDiag1 vs a = iud where
	iud = memo2 inv
	inv i k | i>k = 0
		| i==k = 1
		| otherwise = - sum [iud i j * a j k | j<-vs, j<k]

-- Signatur einer symmetrischen Matrix: (positive, null, negative) Eigenwerte
-- Der Koeffizientenbereich muss ein Koerper sein, um gigantische Zahlen zu vermeiden 
-- www.cas.mcmaster.ca/~cs777/presentations/voicu.pdf 
signature vs m = if el1/=0 then alg1 v1 else 
	if el2/=0 then alg2 v2 else (0,fromIntegral $ length vs,0) where 
	(el1,v1) = piv1 [] vs; (el2,v2) = piv2 [] vs 
	piv1 acc [] = (0, acc)
	piv1 acc (i:r) = if el /= 0 then (el, i:acc++r) else piv1 (i:acc) r where el = m i i
	alg1 (i:r) = if el1 < 0 then (a,b,c+1) else (a+1,b,c) where
		(a,b,c) = signature r mm 
		mi = memo (m i)
		mm p q = m p q - mi p * mi q / el1
	piv2 acc [] = (0,acc)
	piv2 acc (i:r) = p [] r where
		p a2 [] = piv2 (i:acc) r
		p a2 (j:s) = if el/=0 then (el,i:j:acc++a2++s) else p (j:a2) s where el = m j i
	alg2 (i:j:r) = (a+1,b,c+1) where
		(a,b,c) = signature r mm
		mi = memo (m i); mj = memo (m j)
		mm p q =  m p q - (mi p * mj q + mi q * mj p) / el2

