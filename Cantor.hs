module Cantor where

-- Cantor-Konkatenationen von (unendlichen) Listen, 
-- alle Listenelemente der Eingabe kommen in der Ausgabe vor
cantor :: [[a]] -> [a]
cantor = c 1 where
	c _ [] = []
	c n a = mh tna where 
		tna = take n a 
		mh [] = c (n+1) (mt tna)
		mh ([]:r) = mh r
		mh ((a:_):r) = a : mh r 
		mt [] = drop n a
		mt ([]:r) = mt r
		mt ((_:b):r) = b : mt r 
	

-- Cantorsches Polynom
-- cantor [[cantorPoly i j | j<-[0..]]| i<-[0..]] == [0..]
cantorPoly x y = ((x+y)^2 + 3*x + y) `div` 2