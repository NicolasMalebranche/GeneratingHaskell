module SparseLinearAlgebra where

-- Erweiterung zum Modul LinearAlgebra

import LinearAlgebra
import Data.List.Ordered


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

instance (Num a, HasTrie i, Ord j) => MElem (i->[(j,a)]) i j a [(j,a)] where
	mElem = (vElem .) . mRow  
	mRow = id

-- Instanz fuer Sparse-Matrizen * Funktions-Vektoren
instance (Num a, HasTrie i, Ord j) => MV (j,j) (i->[(j,a)]) (j->a) (i->a) where
	mV ab m v = memo f where
		f i = sum [ x * v j | (j,x) <- isectRange ab $ m i]

-- Instanz fuer Sparse-Matrizen * Sparse-Vektoren
instance (Num a, HasTrie i, Ord j) => MV (j,j) (i->[(j,a)]) [(j,a)] (i->a) where
	mV ab m v = memo f where
		f i = vV ab (m i) v


instance (Num a, Ord j) => VM [i] (i->a) (i->[(j,a)]) [(j,a)] where
	vM vs v m = map (\t -> (fst $ head t, foldr ((+).snd) 0 t)) $ 
		groupBy ((.fst).(==).fst) $	foldr (mergeBy ((.fst).compare.fst)) [] $ 
		[ [(j, v i*x) | (j,x) <- m i] | i<-vs]


-- Sparse-Vektoren: (Ord i, Num a) => [(i,a)]
isectRange (a,b) = takeWhile ((<=b).fst) . dropWhile ((<a).fst)

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
