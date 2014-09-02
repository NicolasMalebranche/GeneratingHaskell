{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor, FunctionalDependencies, FlexibleInstances #-}
module LinearAlgebra where

import Data.MemoTrie
import Data.List

-- Rudimentäres Modul für Lineare Algebra
-- Vektoren sind Funktionen ihrer Indizes

delta i j = if i==j then 1 else 0
nullv _ = 0
nullm _ _ = 0
fork op g h i = op (g i) (h i) 

-- flip ist Transposition

-- Definiert eine Matrix aus Liste von Zeilen
defm l = memo2 f where
	f i j = l !! i !! j

-- Matrixmultiplikation
-- vs (vector space) ist die Liste der Indizes, über die 
-- summiert wird, m1, m2 sind die Matrizen
mM vs m1 m2 = memo2 m where 
	m i k = sum [m1 i j * m2 j k | j<-vs]

-- Vektor mal Matrix. In dieser Reihenfolge
vM vs v m = memo vm where
	vm i = sum [v j * m j i | j<-vs]

-- Spur einer Matrix
trace vs m = sum [m j j | j<-vs]

-- Stellt Vektor als Zeile dar
showv vs v = "[\t" ++ concat raw ++ "\t]" where
	raw = intersperse "\t" [show $ v j | j<-vs]

-- Stellt Matrix dar. vs1 für die Zeilen, vs2 für die Spalten
showM vs1 vs2 m = "[" ++ concat raw ++ "]" where
	raw = intersperse "\n" [showv vs2 $ m j | j <- vs1 ]

-- Zeigt Vektor als Zeile an
printv vs v = putStrLn $ showv vs v

-- Zeigt Matrix an
printM vs1 vs2 m = putStrLn $ showM vs1 vs2 m

-- Wandet Matrix (als Funktion ihrer Indizes) in Sparse Matrix um
toSparse m cols = sm where
	sm = memo sm'
	sm' r = [(c, x) | c<-cols, let x=m r c, x/=0]

-- Multipliziert Sparse Matrix von links an eine normale Matrix.
-- Ergebnis ist eine normale Matrix
sparseMul sm m i j = s 0 (sm i) where
	s acc [] = acc
	s acc ((k,x):r) = s (acc + x*m k j) r

-- Multipliziert Sparse Matrix mit Transponiertem von einer Sparse Matrix.
-- Ergebnis ist eine normale Matrix
sparseMulTrans left right i j = s 0 (left i) (right j) where
	s acc [] _ = acc
	s acc _ [] = acc
	s acc v@((i,x):xr) w@((j,y):yr) | i==j = s (acc+x*y) xr yr
		| i < j = s acc xr w
		| otherwise = s acc v yr
