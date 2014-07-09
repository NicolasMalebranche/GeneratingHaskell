{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor, UndecidableInstances, FlexibleInstances #-}
module MatrixAlgorithms where

import Data.MemoTrie
import LinearAlgebra

-- Hilfsfunktinoen für Lineare Algebra

-- Berechnet die Koeffizienten des charakteristischen
-- Polynoms mit dem Algorithmus von Berkowitz.
-- Die Determinante ist das letzte Listenelement.
-- vs sind die Indizes der quadratischen Matrix m
berkowitz vs m = let 
	c j = memo2 toep where
		ii = vs!!(j-1)
		toep i k | k>i = 0
			| k==i = 1
			| otherwise = - rms !! (i-k-1)
		rms = [m ii ii | m <- mpowers]
		mpowers = m : map (mM (take (j-1) vs) m) mpowers
	p 0 = delta
	p j = mM [0..j+1] (c j) (p (j-1)) 
	n = length vs
	pn = p n
	in [pn i 0 | i <-[0..n]]

-- Invertiert untere Dreiecksmatrix, deren Diagonaleinträge gleich 1 sind
invertLowerDiag vs a = ild where
	ild = memo2 inv
	inv i k | i<k = 0
		| i==k = 1
		| otherwise = - sum [a i j * ild j k | j<-vs, i>j]

-- Invertiert obere Dreiecksmatrix, deren Diagonaleinträge gleich 1 sind
invertUpperDiag vs a = iud where
	iud = memo2 inv
	inv i k | i>k = 0
		| i==k = 1
		| otherwise = - sum [iud i j * a j k | j<-vs, j<k]