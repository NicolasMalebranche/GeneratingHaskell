{-# LANGUAGE DeriveFunctor #-}
module AssociativeTest where

-- C steht für eine sich öffnende Klammer, V a für einen Wert
data BracketExpression a = C | V a deriving Functor

showBrackets s = evalBra bra $ map (fmap show) s where
	bra a b = "["++a++","++ b++"]"


data Kind a = Zero a | Succ (a -> Kind a)

-- Wertet einen Ausdruck aus verschachtelten binären Klammern aus
-- f a b ist die Auswertung von [a,b]
-- Man schreibt nur die öffnenden Klammern und die Werte in eine Liste
-- Die öffnenden Klammern am Anfang kann man auch weglassen
-- Beispiel: showBrackets $ map V [1,2,3,4,5]
evalBra f = go $ Succ Zero where
	go (Zero a) [] = a
	go (Zero a) (V b:r) = go (Zero $ f a b) r
	go (Zero a) (C : r) = go (Succ g2) r where
		g2 x = Succ $ Zero . f a . f x
	go (Succ g) (V b:r) = go (g b) r
	go (Succ g) (C  :r) = go (Succ gN) r where
		gN x = Succ $ g . f x
