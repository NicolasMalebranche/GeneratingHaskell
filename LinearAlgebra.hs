{-# LANGUAGE FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses, UndecidableInstances, EmptyDataDecls #-}
module LinearAlgebra where

import Prelude hiding (foldr)
import Data.List hiding (foldr)
import Data.Foldable(Foldable,foldr)
import Data.MemoTrie
import Data.Array


-- Generische Klassen für Lineare Algebra

-- Standardimplementierung für Matrizen: Memoisierte Indexfunktionen
-- Alternative: Arrays
-- Der Koeffizientenbereich für Dense-Matrizenist nicht Teil 
-- des Matrixdatums, sondern muss jedesmal separat angegeben werden. 
-- Das bedeutet kostenlose Vertauschung bzw. Auswahl von Spalten und Zeilen

-----------------------------------------------------------------------------------------
-- Klassen für Datenstrukturen
-- Klasse für Vektoren
class VElem vector index value | vector -> index value where
	vElem :: vector -> index -> value

-- Zeigt an, daß ein Vektor dense ist und seine Indizes nicht selbst speichert
class VElem vector index value => DenseVector vector index value | vector -> index value

-- Klasse für Matrizen
class MElem matrix index1 index2 value | matrix -> index1 index2 value where
	mElem :: matrix -> index1 -> index2 -> value

-- Zeigt an, daß eine Matrix dense ist und ihre Indizes nicht selbst speichert
class MElem matrix index1 index2 value => DenseMatrix matrix index1 index2 value| matrix -> index1 index2 value


instance DenseVector (i->a) i a
instance VElem (i->a) i a where
	vElem = id

instance Ix i => DenseVector (Array i a) i a
instance Ix i => VElem (Array i a) i a where
	vElem = (!)


instance DenseMatrix (i->j->a) i j a 
instance MElem (i->j->a) i j a where
	mElem = id

instance (Ix i, Ix j) => DenseMatrix (Array (i,j) a) i j a 
instance (Ix i, Ix j) => MElem (Array (i,j) a) i j a where
	mElem m i j = m!(i,j)

newtype IndexRange r = IRange r


-----------------------------------------------------------------------------------------
-- Klassen, die Operationen definieren

-- Klasse für Skalarprodukte
class VV range vect1 vect2 value | vect1 -> value , vect2 -> value where
	vV :: range -> vect1 -> vect2 -> value

instance (Num a, Foldable r, DenseVector v1 i a, DenseVector v2 i a) 
	=> VV (IndexRange (r i)) v1 v2 a where
	vV (IRange vs) v w = foldr multplus 0 vs where
		multplus i a = vElem v i * vElem w i + a
instance (Num a, DenseVector v1 i a, DenseVector v2 i a) => VV [i] v1 v2 a where
	vV = vV . IRange


class VSquare range vect value | vect -> value where
	vSquare :: range -> vect -> value

instance (Num a, Foldable r, DenseVector v i a) =>
	VSquare (IndexRange (r i)) v a where
	vSquare (IRange vs) v = foldr (\i s -> vElem v i ^ 2 + s) 0 vs
instance (Num a, DenseVector v i a) => VSquare [i] v a where
	vSquare = vSquare . IRange

-- Zeilenextrakion
class MRow m i row | m i -> row where 
	mRow :: m -> i -> row

instance MRow (i->j->a) i (j->a) where mRow = id

instance (Ix i, Ix j) => MRow (Array (i,j) a) i (Array j a) where
	mRow m i = listArray (a,b) [ m!(i,j) | j<-range(a,b) ] where
		((_,a),(_,b)) = bounds m


-- Definiert die Operation "Matrix mal Vektor"
class MV range matrix vector output | matrix vector -> output where
	mV :: range -> matrix -> vector -> output

instance (Num a, Foldable r, HasTrie i, DenseVector v j a) 
	=> MV (IndexRange (r j)) (i->j->a) v (i->a) where
	mV (IRange vs) m v = memo $ \i-> foldr (multplus i) 0 vs  where 
		multplus i j a = mElem m i j * vElem v j + a
instance (Num a, HasTrie i, DenseVector v j a) 
	=> MV [j] (i->j->a) v (i->a) where mV = mV . IRange

instance (Num a, Foldable r, Ix i, Ix j, DenseVector v j a) 
	=> MV (IndexRange (r j))  (Array (i,j) a) v (Array i a) where
	mV (IRange vs) m v = listArray (a,b) [foldr (multplus i) 0 vs | i<- range (a,b)] where 
		multplus i j a = mElem m i j * vElem v j + a
		((a,_),(b,_)) = bounds m
instance (Num a, Ix i, Ix j, DenseVector v j a) 
	=> MV [j] (Array (i,j) a) v (Array i a) where mV = mV . IRange

-- Definiert die Operation "Vektor mal Matrix"
class VM range vector matrix output | matrix vector -> output where
	vM :: range -> vector -> matrix -> output

instance (Num a, Foldable r, HasTrie j, DenseVector v i a)
	=> VM (IndexRange(r i)) v (i->j->a) (j->a) where
	vM (IRange vs) v m = memo $ \ j -> foldr (multplus j) 0 vs  where 
		multplus j i a = vElem v i * mElem m i j + a
instance (Num a, HasTrie j, DenseVector v i a) 
	=> VM [i] v (i->j->a) (j->a) where vM = vM . IRange

instance (Num a, Foldable r, Ix i, Ix j, DenseVector v i a) 
	=> VM (IndexRange(r i)) v (Array (i,j) a) (Array j a) where
	vM (IRange vs) v m = listArray (a,b) [foldr (multplus j) 0 vs | j<- range (a,b)] where 
		multplus j i a = vElem v i * mElem m i j + a
		((_,a),(_,b)) = bounds m
instance (Num a, Ix i, Ix j, DenseVector v i a) 
	=> VM [i] v (Array (i,j) a) (Array j a) where vM = vM . IRange

-- Definiert die Operation "Matrix mal Matrix"
class MM range matrix1 matrix2 output | matrix1 matrix2 -> output where
	mM :: range -> matrix1 -> matrix2 -> output
	
instance (Num a, HasTrie i, HasTrie k, Foldable r) 
	=> MM (IndexRange(r j)) (i->j->a) (j->k->a) (i->k->a) where
	mM (IRange vs) m n = memo2 $ \i k -> foldr (\j s->m i j * n j k + s) 0 vs
instance (Num a, HasTrie i, HasTrie k) 
	=> MM [j] (i->j->a) (j->k->a) (i->k->a) where mM = mM . IRange

instance (Num a, Ix i, Ix j, Ix k, Foldable r) => 
	MM (IndexRange(r j)) (Array (i,j) a) (Array (j,k) a) (Array (i,k) a) where
	mM (IRange vs) m n = array b [((i,k),f i k) | (i,k) <- range b] where
		((ini,_),(axi,_)) = bounds m
		((_,ink),(_,axk)) = bounds n
		b = ((ini,ink),(axi,axk))
		f i k = foldr (\j s -> m!(i,j)*n!(j,k) + s) 0 vs
instance (Num a, Ix i, Ix j, Ix k) => 
	MM [j] (Array (i,j) a) (Array (j,k) a) (Array (i,k) a) where
	mM = mM . IRange

-- Spur einer Matrix
mTrace vs m = foldr (\i s -> mElem m i i + s) vs

-- Skalarprodukt fuer Matrizen
--mScalarN vs1 vs2 m n = sum [vV vs2 (mRow m i) (mRow n i) | i<-vs1 ]

-- Skalarprodukt mit sich selber, Normquadrat
--mScalarM vs m = mScalarN vs vs m m

delta i j = if i==j then 1 else 0
nullv _ = 0
nullm _ _ = 0
fork op g h i = op (g i) (h i) 


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

