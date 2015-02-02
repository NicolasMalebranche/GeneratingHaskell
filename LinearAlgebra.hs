{-# LANGUAGE FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses, UndecidableInstances #-}
module LinearAlgebra where

import Data.MemoTrie
import Data.List
import Data.Array


-- Klassen für Lineare Algebra

-- Standardimplementierung fuer Matrizen: Memoisierte Indexfunktionen
-- Alternative: Arrays
-- Der Koeffizientenbereich ist nicht Teil des Matrixdatums, sondern 
-- muss jedesmal separat angegeben werden. Das bedeutet kostenlose 
-- Vertauschung bzw. Auswahl von Spalten und Zeilen

-- Hier sollten i, j jeweils HasTrie instantiieren
type FVect i a = i -> a
type FMat i j a = i -> j -> a

-- Hier sollten i, j jeweils Ix instantiieren
type AVect i a = Array i a
type AMat i j a = Array (i,j) a

-- Diagonale Matrizen können als Vektoren gespeichert werden
newtype DiagonalMatrix v = DiagonalMatrix v


-- Klasse fuer Vektoren
class VElem vector index value | vector -> index value where
	vElem :: vector -> index -> value

instance VElem (i->a) i a where
	vElem = id

instance Ix i => VElem (Array i a) i a where
	vElem = (!)


-- Klasse fuer Skalarprodukte
class VV range vector index value | vector -> index value, range -> index where
	vV :: range -> vector -> vector -> value

instance Num a => VV [i] (i->a) i a where
	vV vs v w = sum [v i * w i | i <- vs]

instance (Num a, Ix i) => VV [i] (Array i a) i a where
	vV vs v w = sum [v!i * w!i | i <- vs]


-- Klasse fuer Matrizen
class MElem matrix index1 index2 value row | matrix -> index1 index2 value row where
	mElem :: matrix -> index1 -> index2 -> value
	mRow  :: matrix -> index1 -> row

instance MElem (i->j->a) i j a (j->a) where
	mElem = id
	mRow  = id

instance (Ix i, Ix j) => MElem (Array (i,j) a) i j a (Array j a) where
	mElem m i j = m!(i,j)
	mRow m = let ((_,a),(_,b)) = bounds m  
		in \i -> listArray (a,b) $ map (mElem m i) $ range (a,b)

instance (Num a, Eq i, VElem v i a) => MElem (DiagonalMatrix v) i i a (i->a) where
	mElem (DiagonalMatrix v) i j = if i==j then vElem v i else 0
	mRow = mElem


-- Definiert die Operation "Matrix mal Vektor"
class MV range matrix vector output | matrix vector -> range output where
	mV :: range -> matrix -> vector -> output

instance (Num a, HasTrie i, VElem v j a) => MV [j] (i->j->a) v (i->a) where
	mV vs m v = memo f where 
		f i = sum [ m i j * vElem v j | j <- vs ]

instance (Num a, Ix i, Ix j, VElem v j a) => MV [j] (Array (i,j) a) v (Array i a) where
	mV vs m v = listArray (li,ui) $ map f $ range (li,ui) where
		((li,_),(ui,_)) = bounds m
		f i = sum [ m!(i,j) * vElem v j | j <- vs ] 

instance (Num a, VElem v i a) => MV [i] (DiagonalMatrix v) v (i->a) where
	mV _ (DiagonalMatrix m) v i = vElem m i * vElem v i


-- Definiert die Operation "Vektor mal Matrix"
class VM range vector matrix output | vector matrix -> range output where
	vM :: range -> vector -> matrix -> output

instance (Num a, HasTrie j, VElem v i a) => VM [i] v (i->j->a) (j->a) where
	vM vs v m = memo f where
		f j = sum [ vElem v i * m i j | i <- vs ]

instance (Num a, Ix i, Ix j, VElem v i a) => VM [i] v (Array (i,j) a) (Array j a) where
	vM vs v m = listArray (lj,uj) $ map f $ range (lj,uj) where
		((_,lj),(_,uj)) = bounds m
		f j = sum [ vElem v i * m!(i,j) | i <- vs ]

instance (Num a, VElem v i a) => VM [i] v (DiagonalMatrix v) (i->a) where
	vM _ v (DiagonalMatrix m) i = vElem v i * vElem m i


-- Definiert die Operation "Matrix mal Matrix"
class MM range matrix1 matrix2 output | matrix1 matrix2 -> range output where
	mM :: range -> matrix1 -> matrix2 -> output
	
instance (Num a, HasTrie i, HasTrie j, HasTrie k) =>
	MM [j] (i->j->a) (j->k->a) (i->k->a) where
	mM vs m n = memo2 $ \i k -> sum [ m i j * n j k | j<-vs ]

instance (Num a, Ix i, Ix j, Ix k) => 
	MM [j] (Array (i,j) a) (Array (j,k) a) (Array (i,k) a) where
	mM vs m n = array b [((i,k),f i k) | (i,k) <- range b] where
		((ini,_),(axi,_)) = bounds m
		((_,ink),(_,axk)) = bounds n
		b = ((ini,ink),(axi,axk))
		f i k = sum [m!(i,j)*n!(j,k) | j<-vs]

instance (Num a, VElem v i a) => MM [i] (DiagonalMatrix v) (i->j->a) (i->j->a) where
	mM _ (DiagonalMatrix v) m i = let ve=vElem v i in \j->ve* m i j

instance (Num a, VElem v i a,Ix i, Ix j) => 
	MM [i] (DiagonalMatrix v) (Array (i,j) a) (Array (i,j) a) where
	mM _ (DiagonalMatrix v) m = array (bounds m) 
		[((i,j),vElem v i*a) | ((i,j),a)<-assocs m]

instance (Num a, VElem v j a) => MM [j] (i->j->a) (DiagonalMatrix v) (i->j->a) where
	mM _ m (DiagonalMatrix v) i j = m i j * vElem v j

instance (Num a, VElem v j a, Ix i, Ix j) => 
	MM [i] (Array (i,j) a) (DiagonalMatrix v) (Array (i,j) a) where
	mM _ m (DiagonalMatrix v) = array (bounds m) 
		[((i,j),a*vElem v j) | ((i,j),a)<-assocs m]

instance (Num a, VElem m i a, VElem n i a) => 
	MM [i] (DiagonalMatrix m) (DiagonalMatrix n) (DiagonalMatrix (i->a)) where
	mM _ (DiagonalMatrix m) (DiagonalMatrix n) = DiagonalMatrix $ \i-> vElem m i*vElem n i

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

