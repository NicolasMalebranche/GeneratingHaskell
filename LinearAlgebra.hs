{-# LANGUAGE FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses #-}
module LinearAlgebra2 where

import Data.MemoTrie
import Data.List
import Data.Array
import qualified Data.IntMap as IM


-- Klassen für Lineare Algebra


-- Definiert die Operation "Matrix mal Vektor"
class MV range matrix vector output | matrix vector -> range output where
	mv :: range -> matrix -> vector -> output

-- Instanz fuer Indexfunktionen
instance (Num a, HasTrie i) => MV [j] (i->j->a) (j->a) (i->a) where
	mv vs m v = memo f where 
		f i = sum [ m i j * v j | j <- vs ]

-- Instanz fuer Sparse-Matrizen
instance (Num a, HasTrie i) => MV [Int] (i->IM.IntMap a) (Int->a) (i->a) where
	mv vs m v = memo f where
		vv = IM.fromList [(j,x) | j<-vs, let x = v j, x/=0]
		f i = IM.fold (+) 0 $ IM.intersectionWith (*) vv $ m i

-- Instanz fuer Arrays
instance (Num a, Ix i, Ix j) => MV [j] (Array (i,j) a) (Array j a) (Array i a) where
	mv vs m v = listArray (li,ui) $ map f $ range (li,ui) where
		((li,_),(ui,_)) = bounds m
		f i = sum [ m!(i,j) * v!j | j <- vs ] 



-- Definiert die Operation "Vektor mal Matrix"
class VM range vector matrix output | vector matrix -> range output where
	vM :: range -> vector -> matrix -> output

-- Instanz fuer Indexfunktionen
instance (Num a, HasTrie j) => VM [i] (i->a) (i->j->a) (j->a) where
	vM vs v m = memo f where
		f j = sum [ v i * m i j | i <- vs ]

-- Instanz fuer Sparse-Matrizen
instance Num a => VM [i] (i->a) (i->IM.IntMap a) (IM.IntMap a) where
	vM vs v m = IM.fromListWith (+)
		[ (j, v i * x) | i <- vs, (j,x) <- IM.toList $ m i ]

-- Instanz fuer Arrays
instance (Num a, Ix i, Ix j) => VM [i] (Array i a) (Array (i,j) a) (Array j a) where
	vM vs v m = listArray (lj,uj) $ map f $ range (lj,uj) where
		((_,lj),(_,uj)) = bounds m
		f j = sum [ v!i * m!(i,j) | i <- vs ]



-- Klasse fuer Matrizen
class MElem matrix index1 index2 value | matrix -> index1 index2 value where
	mElem :: matrix -> index1 -> index2 -> value

instance MElem (i->j->a) i j a where
	mElem = id

instance MElem (i->IM.IntMap a) i Int a where
	mElem m i j = m i IM.! j 

instance (Ix i, Ix j) => MElem (Array (i,j) a) i j a where
	mElem m i j = m!(i,j)



-- Klasse fuer Vektoren
class VElem vector index value | vector -> index value where
	vElem :: vector -> index -> value

instance VElem (i->a) i a where
	vElem = id

instance VElem (IM.IntMap a) Int a where
	vElem = (IM.!)

instance Ix i => VElem (Array i a) i a where
	vElem = (!)


-- Spur einer Matrix
trace vs m = sum [mElem m j j | j<-vs]

delta i j = if i==j then 1 else 0
nullv _ = 0
nullm _ _ = 0
fork op g h i = op (g i) (h i) 

-- flip ist Transposition


-- Stellt Vektor als Zeile dar
showv vs v = "[\t" ++ concat raw ++ "\t]" where
	raw = intersperse "\t" [show $ vElem v j | j<-vs]

-- Stellt Matrix dar. vs1 für die Zeilen, vs2 für die Spalten
showM vs1 vs2 m = "[" ++ concat raw ++ "]" where
	raw = intersperse "\n" [showv vs2 $ mElem m j | j <- vs1 ]

-- Zeigt Vektor als Zeile an
printv vs v = putStrLn $ showv vs v

-- Zeigt Matrix an
printM vs1 vs2 m = putStrLn $ showM vs1 vs2 m

-- Definiert eine Matrix aus Liste von Zeilen
defm l = memo2 f where
	f i j = l !! i !! j

-- Matrixmultiplikation
-- vs (vector space) ist die Liste der Indizes, über die 
-- summiert wird, m1, m2 sind die Matrizen
mM vs m1 m2 = memo2 m where 
	m i k = sum [m1 i j * m2 j k | j<-vs]

-- Wandet Matrix (als Funktion ihrer Indizes) in Sparse Matrix um
toSparse m cols = sm where
	sm = memo sm'
	sm' r = [(c, x) | c<-cols, let x=m r c, x/=0]

-- Multipliziert Sparse Matrix von links an eine normale Matrix.
-- Ergebnis ist eine normale Matrix
sparseMul sm m i j = s 0 (sm i) where
	s acc [] = acc
	s acc ((k,x):r) = s (acc + x*m k j) r

-- Multipliziert Matrix von links mit Transponiertem von einer Sparse Matrix
-- Ergebnis ist eine normale Matrix
mulSparse m sm i j = s 0 (sm j) where
	s acc [] = acc
	s acc ((k,x):r) = s (acc + m i k*x) r

-- Multipliziert Sparse Matrix mit Transponiertem von einer Sparse Matrix.
-- Ergebnis ist eine normale Matrix
sparseMulTrans left right i j = s 0 (left i) (right j) where
	s acc [] _ = acc
	s acc _ [] = acc
	s acc v@((i,x):xr) w@((j,y):yr) | i==j = s (acc+x*y) xr yr
		| i < j = s acc xr w
		| otherwise = s acc v yr
