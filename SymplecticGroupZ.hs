{-# LANGUAGE MultiParamTypeClasses, OverlappingInstances #-}
module SymplecticGroupZ where

import GroupAction
import Elementary

-- Symplektische Gruppe über den ganzen Zahlen
-- http://mathoverflow.net/q/65941/62593
-- Sp(2n,Z) wird erzeugt von SpD und SpJ für n>3
-- und von SpD, SpR und SpT für n<=3
data SpZ = SpD | SpJ | SpR | SpT deriving (Show,Eq,Enum)

instance (Num a) => GroupAction SpZ [a] where
	gAct SpD = symplecticD
	gAct SpJ = symplecticR21 . symplecticTn
	gAct SpR = symplecticR21
	gAct SpT = symplecticTn

-- Die Basis ist geordnet als [a,a*,b,b*,c,c*..]
symplecticForm [] [] = 0
symplecticForm (a:b:x) (c:d:y) = a*d - b*c + symplecticForm x y
symplecticForm _ _ = error "symplectic form not well-defined"

symplecticD [] = []
symplecticD (a:b:x) = x ++ [ -b, a] 

symplecticR21 [] = []
symplecticR21 [a,b] = [a,b]
symplecticR21 (a:b:c:d:x) = (a+c):b:c:(d-b):x

symplecticT1 [] = []
symplecticT1 (a:b:x) = (a+b):b:x

symplecticTn [] = []
symplecticTn [a,b] = [a+b,b]
symplecticTn (a:b:x) = a:b: symplecticTn x
