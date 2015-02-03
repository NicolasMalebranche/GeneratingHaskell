{-# LANGUAGE FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses, UndecidableInstances, EmptyDataDecls #-}
module SparseLinearAlgebra where

-- Erweiterung zum Modul LinearAlgebra

import LinearAlgebra
import Data.List
import Data.List.Ordered
import Data.MemoTrie

-- Diagonale Matrizen können als Vektoren gespeichert werden
newtype DiagonalMatrix v = DiagonalMatrix v

type SparseMatrix i j a = i->[(j,a)]

--Hilfsfunktionen
isectRange (a,b) = takeWhile ((<=b).fst) . dropWhile ((<a).fst)
inRange (a,b) i = a<=i && i<=b

-- Zaehlt endliche Anzahl von Sparse-Vektoren zusammen
combineSparse vecs = map (\t -> (fst $ head t, foldr ((+).snd) 0 t)) $ 
		groupBy ((.fst).(==).fst) $	foldr (mergeBy ((.fst).compare.fst)) [] vecs



-- Sparse Vektoren
instance (Num a, Ord i) => VElem [(i,a)] i a where
	vElem v i = case isectBy ((.fst).compare.fst) v [(i,undefined)] of
		{ [] -> 0;  [(_,a)] -> a }

instance (Ord i, Num a) => VV (i,i) [(i,a)] i a where
	vV ab v w = let 
		iw = isectRange ab w 
		multplus [(_,x),(_,y)] r = x*y + r
		multplus _ r = r
		in foldr multplus 0 $ groupBy ((.fst).(==).fst) $ 
			mergeBy ((.fst).compare.fst) v iw

-- MElem Instanzen
instance (Num a, HasTrie i, Ord j) => MElem (i->[(j,a)]) i j a [(j,a)] where
	mElem = (vElem .) . mRow  
	mRow = id

instance (Num a, Eq i, VElem v i a) => MElem (DiagonalMatrix v) i i a (i->a) where
	mElem (DiagonalMatrix v) i j = if i==j then vElem v i else 0
	mRow = mElem


-- MV Instanzen
instance (Num a, HasTrie i, Ord j) => MV (j,j) (i->[(j,a)]) (j->a) (i->a) where
	mV ab m v = memo f where
		f i = sum [ x * v j | (j,x) <- isectRange ab $ m i]

instance (Num a, HasTrie i, Ord j) => MV (j,j) (i->[(j,a)]) [(j,a)] (i->a) where
	mV ab m v = memo f where
		f i = vV ab (m i) v

instance (Num a, Ord i, VElem v i a) => MV (i,i) (DiagonalMatrix v) (i->a) (i->a) where
	mV ab (DiagonalMatrix v) w i = if inRange ab i then vElem v i * w i else 0

instance (Num a, Ord i, VElem v i a) => MV (i,i) (DiagonalMatrix v) [(i,a)] [(i,a)] where
	mV ab (DiagonalMatrix v) w = [ (i,vElem v i * a) | (i,a) <- isectRange ab w]


-- VM Instanzen
instance (Num a, Ord i, Ord j) => VM (i,i) [(i,a)] (i->[(j,a)]) [(j,a)] where
	vM ab v m = combineSparse [ [(j, x*y) | (j,y) <- m i] | (i,x)<- isectRange ab v]

instance (Num a, Ord j) => VM [i] (i->a) (i->[(j,a)]) [(j,a)] where
	vM vs v m = combineSparse [ [(j, v i*x) | (j,x) <- m i] | i<-vs]

instance (Num a, Ord i, VElem v i a) => VM (i,i) (i->a) (DiagonalMatrix v) (i->a) where
	vM ab w (DiagonalMatrix v) i = if inRange ab i then w i * vElem v i else 0

instance (Num a, Ord i, VElem v i a) => VM (i,i) [(i,a)] (DiagonalMatrix v) [(i,a)] where
	vM ab w (DiagonalMatrix v) = [ (i, a * vElem v i) | (i,a) <- isectRange ab w]


-- MM Instanzen
instance (Num a, Ord i, VElem d i a) =>
	MM (i,i) i i j a (DiagonalMatrix d) (i->j->a) (i->j->a) where
	mM ab (DiagonalMatrix d) m i = if inRange ab i then \j-> vElem d i * m i j else const 0

instance (Num a, Ord i, VElem d i a) =>
	MM (i,i) i i j a (DiagonalMatrix d) (i->[(j,a)]) (i->[(j,a)]) where
	mM ab (DiagonalMatrix d) m i = 
		if inRange ab i then [(j,dd*a) | let dd=vElem d i, (j,a)<-m i] else []

instance (Num a, Ord i, VElem d i a, VElem v i a) =>
	MM (i,i) i i i a (DiagonalMatrix d) (DiagonalMatrix v) (DiagonalMatrix (i->a)) where
	mM ab (DiagonalMatrix d) (DiagonalMatrix v) = DiagonalMatrix $ 
		\ i -> if inRange ab i then vElem d i * vElem v i else 0

instance (Num a, Ord j, VElem d j a) =>
	MM (j,j) i j j a (i->j->a) (DiagonalMatrix d) (i->j->a) where
	mM ab m (DiagonalMatrix d) i j = if inRange ab j then m i j * vElem d j else 0

instance (Num a, Ord j, VElem d i a) =>
	MM (j,j) i j j a (i->[(j,a)]) (DiagonalMatrix d) (i->[(j,a)]) where
	mM ab m (DiagonalMatrix d) i = [(j,a*dd)| let dd = vElem d i, (j,a)<-m i, inRange ab j]


-- Wandelt Matrix (als Funktion ihrer Indizes) in Sparse Matrix um
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
