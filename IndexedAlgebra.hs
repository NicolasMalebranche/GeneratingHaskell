{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor, FunctionalDependencies, FlexibleInstances, GADTs, UndecidableInstances,
OverlappingInstances #-}
module IndexedAlgebra where

import Data.MemoTrie
import Data.List
import IndexedLinearAlgebra


-- Klasse für Indizes von Algebren
class VectorIndex i => AlgebraIndex i where
	coMult :: Num a => (i->a) -> (i->a) -> (i->a)
	coOne :: Num a => (i->a)

class VectorSpace v r => Algebra v r | v->r where
	vectMult :: v -> v -> v
	vectOne :: v

---- INSTANZEN ----------------------------------------------------------------
-------------------------------------------------------------------------------

-- Memoizable Funktionen von AlgebraIndizes nach Ringen
-- bilden eine Algebra
instance (HasTrie i, AlgebraIndex i, Num r) => Algebra (i->r) r where
	vectMult v w = memo z where z = coMult v w
	vectOne = coOne

instance (Num r, Algebra a r) => Num a where
	(*) = vectMult
	(+) = vectAdd
	negate v = vectScal v (-1)
	signum v = v
	abs v = v
	fromInteger i = vectScal vectOne (fromInteger i)

-- Symmetrische Algebra über einem Modul --
-------------------------------------------
newtype SymmetricFunction i r = SymFun ([i] -> r)
-- Bettet einen Vektor als Grad-1-Element ein
imbedSymmetric :: (VectorIndex i, HasTrie i, Ord i, Num r) => 
	(i -> r) -> SymmetricFunction i r 
imbedSymmetric f = SymFun ff where
	ff [i] =  f i
	ff _ = 0
-- Symmetrisiert einen Tensor
symmetrize :: (VectorIndex i, HasTrie i, Ord i, Num r) => 
	([i] -> r) -> SymmetricFunction i r
symmetrize f = SymFun (memo ff . sort) where
	ff list = sum [f p | p <- permutations list]
-- Macht aus einem symmetrischen Polynom wieder einen normalen Tensor
unSymmetrize :: SymmetricFunction i r -> [i] -> r
unSymmetrize (SymFun f) = f

-- Basen
powerSum k = SymFun p where
	p [] = if k==0 then 1 else 0
	p (x:xs) = if length xs == k-1 && all (x==) xs then 1 else 0
elemSym k = SymFun e where
	alldiff [] = True 
	alldiff (x:xs) = all (x/=) xs && alldiff xs
	e l = if k==length l && alldiff l then 1 else 0

-- Symmetrische Polynome bilden einen Vektorraum
instance (HasTrie i, VectorIndex i, Ord i, Num r) => VectorSpace (SymmetricFunction i r) r where
	vectAdd (SymFun v) (SymFun w) = SymFun $ vectAdd v w
	vectScal (SymFun v)  a = SymFun $ vectScal v a
	vectZero = SymFun vectZero

-- Symmetrische Algebra ist Algebra
instance (HasTrie i, VectorIndex i, Ord i, Num r) => Algebra (SymmetricFunction i r) r where
	vectOne = SymFun onl where
		onl [] = 1
		onl _ = 0
	vectMult (SymFun v) (SymFun w) = SymFun (memo z . sort) where
	-- Permutiert die Indizes unter Berücksichtiung gleicher Indizes
		symPartit m f g (x:xs) = if m == Just x then symPartit m f (g.(x:)) xs  
			else symPartit Nothing (f.(x:)) g xs + symPartit (Just x) f (g.(x:)) xs
		symPartit m f g [] = f [] * g []
		z = symPartit Nothing v w

