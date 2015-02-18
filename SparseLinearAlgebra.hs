{-# LANGUAGE FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses, UndecidableInstances #-}
module SparseLinearAlgebra where

-- Erweiterung zum Modul LinearAlgebra

import LinearAlgebra
import Data.List hiding (foldr)
import Prelude hiding (foldr)
import Data.Foldable(Foldable,foldr)
import Data.List.Ordered
import Data.MemoTrie
import Data.Array

newtype SparseVector v = VSparse v
newtype SparseMatrix m = MSparse m 
newtype DiagonalMatrix d = MDiag d


-- Zaehlt endliche Anzahl von Sparse-Vektoren zusammen
combineSparse vecs = map (\t -> (vbIndex $ head t, foldr ((+).vbValue) 0 t)) $ 
		groupBy ((.vbIndex).(==).vbIndex) $	
		foldr (mergeBy ((.vbIndex).compare.vbIndex)) [] vecs

class IndexValue b i a | b -> i a where
	vbIndex :: b -> i
	vbValue :: b -> a

instance IndexValue (i,a) i a where
	vbIndex = fst
	vbValue = snd


-- VV Instanzen
instance (Foldable c, IndexValue b i a, DenseVector w i a, Num a) 
	=> VV (i->Bool) (SparseVector (c b)) w a where
	vV f (VSparse v) w = foldr (\b s -> vbValue b*vElem w (vbIndex b) + s) 0 v
instance (IndexValue b i a, DenseVector w i a, Num a) => VV (i->Bool) [b] w a where
	vV f = vV f . VSparse

instance (Foldable c, IndexValue b i a, DenseVector v i a, Num a) 
	=> VV (i->Bool) v (SparseVector (c b)) a where
	vV f v (VSparse w) = foldr (\b s -> vElem v (vbIndex b)*vbValue b + s) 0 w
instance (IndexValue b i a, DenseVector v i a, Num a) 
	=> VV (i->Bool) v [b] a where vV f v = vV f v . VSparse

instance (IndexValue b i a, IndexValue b' i a, Ord i, Num a) 
	=> VV (i->Bool) [b] [b'] a where
	vV f = z 0 where
		z s [] _ = s; z s _ [] = s
		z s v@(a:r) w@(b:q) = case compare (vbIndex a) (vbIndex b) of
			EQ -> if f (vbIndex a) then z (s+vbValue a*vbValue b) r q else z s r q
			LT -> z s r w
			GT -> z s v q

-- VSquare Instanzen
instance (Foldable c, IndexValue b i a, Num a) 
	=> VSquare (i->Bool) (SparseVector (c b)) a where
	vSquare f (VSparse v) = foldr (\a s -> if f (vbIndex a) then vbValue a^2 + s else s) 0 v
instance (IndexValue b i a, Num a) => VSquare (i->Bool) [b] a where
	vSquare f = vSquare f . VSparse


-- MRow Instanzen
instance MRow (SparseMatrix (i->r)) i (SparseVector r) where
	mRow (MSparse m) i = VSparse $ m i

instance VElem v i a => MRow (DiagonalMatrix v) i (SparseVector [(i,a)]) where
	mRow (MDiag d) i = VSparse [(i,vElem d i)]

-- MV Instanzen
-- Dense Matrix, Sparse Vector
instance (Num a, Foldable r, HasTrie i, IndexValue b j a) 
	=> MV (j->Bool) (i->j->a) (SparseVector (r b)) (i->a) where
	mV f m (VSparse v) = memo $ \i-> foldr (multplus i) 0 v  where 
		multplus i a s = let j = vbIndex a in if f j then mElem m i j * vbValue a + s else s
instance (Num a, Foldable r, Ix i, Ix j, IndexValue b j a) 
	=> MV (j->Bool) (Array (i,j) a) (SparseVector (r b)) (Array i a) where
	mV f m (VSparse v) = listArray (a,b) [foldr (multplus i) 0 v | i<- range (a,b)] where 
		multplus i a s = let j = vbIndex a in if f j then mElem m i j * vbValue a + s else s
		((a,_),(b,_)) = bounds m
instance (MV f m (SparseVector [b]) o) => MV f m [b] o where
	mV f m = mV f m . VSparse

-- Sparse Matrix, Dense Vector
instance (Num a, HasTrie i, Foldable r, IndexValue b j a, DenseVector v j a) 
	=> MV (j->Bool) (SparseMatrix (i->r b)) v (i->a) where
	mV s (MSparse m) v = memo f where
		f i = foldr (\a u -> let j = vbIndex a in if s j 
			then vbValue a*vElem v j + u else u) 0 (m i)
instance (Num a, HasTrie i, IndexValue b j a, DenseVector v j a) 
	=> MV (j->Bool) (i->[b]) v (i->a) where
	mV s = mV s . MSparse

-- Diagonalmatrix
instance (Num a, VElem d i a) => MV (i->Bool) (DiagonalMatrix d) (i->a) (i->a) where
	mV f (MDiag d) v i = if f i then vElem d i * vElem v i else 0 
instance (Num a, VElem d i a, Ix i) 
	=> MV (i->Bool) (DiagonalMatrix d) (Array i a) (Array i a) where
	mV f (MDiag d) v = v // [ (i,vElem d i * a) |(i,a) <- assocs v , f i]
instance (Num a, VElem d i a, IndexValue b i a, Foldable r) 
	=> MV (i->Bool) (DiagonalMatrix d) (SparseVector (r b)) (SparseVector [(i,a)]) where
	mV f (MDiag d) (VSparse v) = VSparse $ foldr con [] v where
		con b s = let i = vbIndex b in if f i then (i,vElem d i * vbValue b):s else s

-- VM Instanzen
-- Dense Matrix, Sparse Vector
instance (Num a, Foldable r, HasTrie j, IndexValue b i a) 
	=> VM (i->Bool) (SparseVector (r b)) (i->j->a) (j->a) where
	vM f (VSparse v) m = memo $ \j-> foldr (multplus j) 0 v  where 
		multplus j a s = let i = vbIndex a in if f i then vbValue a * mElem m i j + s else s
instance (Num a, Foldable r, Ix i, Ix j, IndexValue b i a) 
	=> VM (i->Bool) (SparseVector (r b)) (Array (i,j) a) (Array j a) where
	vM f (VSparse v) m = listArray (a,b) [foldr (multplus j) 0 v | j<- range (a,b)] where 
		multplus j a s = let i = vbIndex a in if f i then vbValue a * mElem m i j + s else s
		((_,a),(_,b)) = bounds m
instance (VM f (SparseVector [b]) m o) => VM f [b] m o where
	vM f = vM f . VSparse

-- Diagonalmatrix
-- Diagonalmatrix
instance (Num a, VElem d i a) => VM (i->Bool) (i->a) (DiagonalMatrix d) (i->a) where
	vM f v (MDiag d) i = if f i then vElem v i * vElem d i else 0 
instance (Num a, VElem d i a, Ix i) 
	=> VM (i->Bool) (Array i a) (DiagonalMatrix d) (Array i a) where
	vM f v (MDiag d) = v // [ (i, a * vElem d i) |(i,a) <- assocs v , f i]
instance (Num a, VElem d i a, IndexValue b i a, Foldable r) 
	=> VM (i->Bool) (SparseVector (r b)) (DiagonalMatrix d) (SparseVector [(i,a)]) where
	vM f (VSparse v) (MDiag d) = VSparse $ foldr con [] v where
		con b s = let i = vbIndex b in if f i then (i, vbValue b * vElem d i):s else s


-- MM Instanzen
instance (Num a, Foldable r, IndexValue b j a, HasTrie i, HasTrie k) =>
	MM (j->Bool) (SparseMatrix (i->r b)) (j->k->a) (i->k->a) where
	mM s (MSparse m) n = memo2 f where
		f i k = foldr (\a u -> let j = vbIndex a in if s j 
			then vbValue a*mElem n j k + u else u) 0 (m i)

instance (Num a, DenseVector d i a, DenseVector d' i a)
	=> MM (i->Bool) (DiagonalMatrix d) (DiagonalMatrix d') (DiagonalMatrix (i->a)) where
	mM f (MDiag d) (MDiag d') = MDiag dd where
		dd i = if f i then vElem d i * vElem d' i else 0

instance (Num a, DenseVector d i a) 
	=> MM (i->Bool) (DiagonalMatrix d) (i->j->a) (i->j->a) where
	mM f (MDiag d) m i j = if f i then vElem d i * mElem m i j else 0
instance (Num a, DenseVector d j a) 
	=> MM (j->Bool) (i->j->a) (DiagonalMatrix d) (i->j->a) where
	mM f m (MDiag d) i j = if f j then mElem m i j*vElem d j else 0


-- Wandelt Matrix (als Funktion ihrer Indizes) in Sparse Matrix um
toSparse m cols = MSparse sm where
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
