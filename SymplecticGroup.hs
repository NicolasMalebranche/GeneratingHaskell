{-# LANGUAGE MultiParamTypeClasses, OverlappingInstances, FlexibleInstances #-}
module SymplecticGroup where

import GroupAction

-- Symplektische Gruppe über den ganzen Zahlen
-- Die gestrichenen Generatoren bedeuten Inverse
-- http://mathoverflow.net/q/65941/62593
-- Sp(2n,Z) wird erzeugt von SpD, SpJ und SpJ' für n>3
-- von SpD, SpR, SpR', SpT, SpT' für n=2,3
-- und von SpT ,SpT' und SpD für n=1.
-- Man erhält so auch Sp(2n,F_p). 
-- Dann braucht man die gestrichenen nicht.
data Sp = SpT' | SpR' | SpR | SpT | SpD | SpJ | SpJ' 
	deriving (Show,Eq,Enum)

instance (Num a) => GroupAction Sp [a] where
	gAct SpD = symplecticD
	gAct SpJ = symplecticR21 . symplecticTn
	gAct SpJ'= symplecticT_n . symplecticR21_1
	gAct SpR = symplecticR21
	gAct SpR'= symplecticR21_1
	gAct SpT = symplecticT1
	gAct SpT' = symplecticT_1

instance (Num a) => GroupAction Sp [[a]] where
	gAct g = map (gAct g)

-- Die Basis ist geordnet als [a,a*,b,b*,c,c*..]
symplecticForm [] [] = 0
symplecticForm (a:b:x) (c:d:y) = a*d - b*c + symplecticForm x y
symplecticForm _ _ = error "symplectic form not well-defined"

-- Hat Ordnung 4n
symplecticD [] = []
symplecticD (a:b:x) = x ++ [ -b, a] 

symplecticR21 [] = []
symplecticR21 [a,b] = [a,b]
symplecticR21 (a:b:c:d:x) = (a+c):b:c:(d-b):x

symplecticR21_1 [] = []
symplecticR21_1 [a,b] = [a,b]
symplecticR21_1 (a:b:c:d:x) = (a-c):b:c:(d+b):x

symplecticT1 [] = []
symplecticT1 (a:b:x) = (a+b):b:x

symplecticT_1 [] = []
symplecticT_1 (a:b:x) = (a-b):b:x

symplecticTn [] = []
symplecticTn [a,b] = [a+b,b]
symplecticTn (a:b:x) = a:b: symplecticTn x

symplecticT_n [] = []
symplecticT_n [a,b] = [a-b,b]
symplecticT_n (a:b:x) = a:b: symplecticT_n x
