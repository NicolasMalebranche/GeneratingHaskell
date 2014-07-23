module ShowMatrix where

-- Formatiert Matrizen für andere Software

import Data.List

-- Für GAP
showGapMat rows columns m = "a := [\n" ++ mat ++ "\n];" where
	r i = show [m i j | j<- columns]
	mat = concat $ intersperse ",\n" [r i | i<-rows]

-- Für Singular
showSingularMat rows columns m = "intmat A["++show ro ++" ]["++show co++"]=\n" ++ x ++ ";" where
	ro = length rows
	co = length columns
	r i = concat $ intersperse "," [show $ m i j | j<-columns]
	x = concat $ intersperse ",\n" [r i | i<-rows]