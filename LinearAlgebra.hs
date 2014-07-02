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