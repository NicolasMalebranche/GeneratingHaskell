{-# LANGUAGE FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses #-}
module LinearAlgebra where

import Data.MemoTrie
import Data.List
import Data.List.Ordered
import Data.Array


-- Klassen für Lineare Algebra

-- Standardimplementierung fuer Matrizen: Memoisierte Indexfunktionen
-- Der Koeffizientenbereich ist nicht Teil des Matrixdatums, sondern 
-- muss jedesmal separat angegeben werden. Bei Sparse-Zeilenvektoren ist das zwar  
-- etwas laestig, erlaubt jedoch den problemlosen Umgang mit unendlichen Matrizen.
-- Bei den anderen Implementationen ergibt das kostenlose Vertauschung bzw.
-- Auswahl von Spalten und Zeilen

-- Sparse-Vektoren: (Ord i, Num a) => [(i,a)]
isectRange (a,b) = takeWhile ((<=b).fst) . dropWhile ((<a).fst)


-- Klasse fuer Vektoren
class VElem vector index value | vector -> index value where
	vElem :: vector -> index -> value

instance VElem (i->a) i a where
	vElem = id

instance Ix i => VElem (Array i a) i a where
	vElem = (!)

instance (Num a, Ord i) => VElem [(i,a)] i a where
	vElem v i = case isectBy ((.fst).compare.fst) v [(i,undefined)] of
		{ [] -> 0;  [(_,a)] -> a }


-- Klasse fuer Skalarprodukte
class VV range vector index value | vector -> index value, range -> index where
	vV :: range -> vector -> vector -> value

instance Num a => VV [i] (i->a) i a where
	vV vs v w = sum [v i * w i | i <- vs]

instance (Num a, Ix i) => VV [i] (Array i a) i a where
	vV vs v w = sum [v!i * w!i | i <- vs]

instance (Ord i, Num a) => VV (i,i) [(i,a)] i a where
	vV ab v w = let 
		iw = isectRange ab w 
		multplus [(_,x),(_,y)] r = x*y + r
		multplus _ r = r
		in foldr multplus 0 $ groupBy ((.fst).(==).fst) $ 
			mergeBy ((.fst).compare.fst) v iw
	
		

-- Klasse fuer Matrizen
class MElem matrix index1 index2 value row | matrix -> index1 index2 value row where
	mElem :: matrix -> index1 -> index2 -> value
	mRow  :: matrix -> index1 -> row

instance MElem (i->j->a) i j a (j->a) where
	mElem = id
	mRow  = id

instance (Ix i, Ix j) => MElem (Array (i,j) a) i j a (Array j a) where
	mElem m i j = m!(i,j)
	mRow  m = let ((_,a),(_,b)) = bounds m  
		in \i -> listArray (a,b) $ map (mElem m i) $ range (a,b)
		
instance (Num a, HasTrie i, Ord j) => MElem (i->[(j,a)]) i j a [(j,a)] where
	mElem = (vElem .) . mRow  
	mRow = id


-- Definiert die Operation "Matrix mal Vektor"
class MV range matrix vector output | matrix vector -> range output where
	mV :: range -> matrix -> vector -> output

-- Instanz fuer Indexfunktionen
instance (Num a, HasTrie i, VElem v j a) => MV [j] (i->j->a) v (i->a) where
	mV vs m v = memo f where 
		f i = sum [ m i j * vElem v j | j <- vs ]

-- Instanz fuer Sparse-Matrizen * Funktions-Vektoren
instance (Num a, HasTrie i, Ord j) => MV (j,j) (i->[(j,a)]) (j->a) (i->a) where
	mV ab m v = memo f where
		f i = sum [ x * v j | (j,x) <- isectRange ab $ m i]

-- Instanz fuer Sparse-Matrizen * Sparse-Vektoren
instance (Num a, HasTrie i, Ord j) => MV (j,j) (i->[(j,a)]) [(j,a)] (i->a) where
	mV ab m v = memo f where
		f i = vV ab (m i) v

-- Instanz fuer Array-Matrizen 
instance (Num a, Ix i, Ix j, VElem v j a) => MV [j] (Array (i,j) a) v (Array i a) where
	mV vs m v = listArray (li,ui) $ map f $ range (li,ui) where
		((li,_),(ui,_)) = bounds m
		f i = sum [ m!(i,j) * vElem v j | j <- vs ] 



-- Definiert die Operation "Vektor mal Matrix"
class VM range vector matrix output | vector matrix -> range output where
	vM :: range -> vector -> matrix -> output

-- Instanz fuer Indexfunktionen
instance (Num a, HasTrie j, VElem v i a) => VM [i] v (i->j->a) (j->a) where
	vM vs v m = memo f where
		f j = sum [ vElem v i * m i j | i <- vs ]

-- Instanz fuer Sparse-Matrizen
instance (Num a, Ord j) => VM [i] (i->a) (i->[(j,a)]) [(j,a)] where
	vM vs v m = map (\t -> (fst $ head t, foldr ((+).snd) 0 t)) $ 
		groupBy ((.fst).(==).fst) $	foldr (mergeBy ((.fst).compare.fst)) [] $ 
		[ [(j, v i*x) | (j,x) <- m i] | i<-vs]

-- Instanz fuer Arrays
instance (Num a, Ix i, Ix j, VElem v i a) => VM [i] v (Array (i,j) a) (Array j a) where
	vM vs v m = listArray (lj,uj) $ map f $ range (lj,uj) where
		((_,lj),(_,uj)) = bounds m
		f j = sum [ vElem v i * m!(i,j) | i <- vs ]



-- Spur einer Matrix
trace vs m = sum [mElem m j j | j<-vs]

-- Skalarprodukt fuer Matrizen
mScalarN vs1 vs2 m n = sum [vV vs2 (mRow m i) (mRow n i) | i<-vs1 ]

-- Skalarprodukt mit sich selber, Normquadrat
mScalarM vs m = mScalarN vs vs m m

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
