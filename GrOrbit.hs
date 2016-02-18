{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
module GrOrbit where

import Data.Set
import Data.List
import CyclotomicField
import GroupAction
import SmallMatrix
import F_p

data E6Group = X | T | S | S_1 deriving (Eq,Show,Enum)

type Eisenstein = CyclotomicField Integer
xi = cycRoot 6 :: Eisenstein

toMatrix X = Mat2 (xi,0,0,1)
toMatrix T = Mat2 (0,1,1,0)
toMatrix S = Mat2 (1,1,0,1)
toMatrix S_1= Mat2(1,-1,0,1)



instance GroupAction E6Group (Eisenstein,Eisenstein) where
	gAct = mV . toMatrix

instance GroupAction E6Group (Matrix2 Eisenstein) where
	gAct = (*) . toMatrix 

newtype Torsion2 =  Tor (F Mod2, F Mod2, F Mod2, F Mod2) deriving (Show,Eq,Ord)
instance GroupAction E6Group Torsion2 where
	gAct X (Tor (a,b,c,d)) = Tor (b,a+b,c,d)
	gAct T (Tor (a,b,c,d)) = Tor (c,d,a,b)
	gAct S (Tor (a,b,c,d)) = Tor (a+c,b+d,c,d)
	gAct S_1 x = gAct S x

torsionTriple u@(Tor (a,b,c,d)) v@(Tor (w,x,y,z)) = 
	fromList [u,v, Tor (a+w,b+x,c+y,d+z)]

triple1 = torsionTriple (Tor (1,0,0,0)) (Tor (0,1,0,0))
triple2 = torsionTriple (Tor (1,0,0,0)) (Tor (0,0,1,0))

-- orbit of length 5
orbit5 = mapM_ print $ toList $ gOrbit [X ..S] triple1

-- orbit of length 30
orbit30 = mapM_ print $ toList $ gOrbit [X ..S] triple2
