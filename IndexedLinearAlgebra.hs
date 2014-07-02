{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor, FunctionalDependencies, FlexibleInstances #-}
module IndexedLinearAlgebra where

import Data.MemoTrie

-- Klasse für Indizes von Vektorräumen,
-- die die Rechenregeln mitdefiniert
class VectorIndex i where
	coAdd  :: Num a => (i->a) -> (i->a) -> (i->a)
	coScal :: Num a => (i->a) -> a -> (i->a)
	coZero :: Num a => (i->a)
	coAdd v w i = v i + w i
	coScal v a i = v i * a
	coZero _ = 0

-- Direkte Summe zweier Vektoren, die durch Indexfunktionen gegeben sind
coSum :: (VectorIndex i, VectorIndex j, Num a) => 
	(i->a) -> (j->a) -> (Either i j -> a)
coSum v w = decide where
	decide (Left i) = v i
	decide (Right j) = w j

-- Tensorprodukt zweier Vektoren, die durch Indexfunktionen gegeben sind
coTensor :: (VectorIndex i, VectorIndex j, Num a) =>
	(i->a) -> (j->a) -> (i->j->a)
coTensor v w i j = v i * w j

-- Identifiziert eine Index-Tensor-Matrix mit einem Homomorphismus
-- Benötigt noch die Information, worüber summiert wird
homify :: (VectorIndex i, VectorIndex j, HasTrie j, Num a) => 
	(j->[i]) -> (i->j->a) -> (i->a) -> (j->a)
homify relevantFor t v = memo w where
	w iw = sum [ t iv iw * v iv | iv <- relevantFor iw]

-- Klasse für Vektorräume/Moduln
-- Der Modul sollte seinen zugrundeliegenden Ring kennen
class Num r => VectorSpace v r | v -> r where
	vectAdd :: v -> v -> v
	vectScal :: v -> r -> v
	vectZero :: v


---- INSTANZEN ----------------------------------------------------------------
-------------------------------------------------------------------------------

instance VectorIndex Int
instance VectorIndex Integer
instance VectorIndex i => VectorIndex [i]

-- Memoizable Funktionen von VektorIndizes nach Ringen
-- bilden einen Modul
instance (HasTrie i, VectorIndex i, Num a) => VectorSpace (i -> a) a where
	vectAdd v w = memo $ coAdd v w
	vectScal v a = memo $ coScal v a
	vectZero i = coZero i

