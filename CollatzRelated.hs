module CollatzRelated where

import Data.Array

data Collatz = Collatz {
	up :: Integer
	,down :: Integer	
	,syr :: Integer -> Integer
	,modulusShifts :: Array Integer Integer
	}

-- Erzeugt die Iterationsfunktion. up ist der Multiplikator, down der Divisor
createCollatz up down = Collatz { up = up, down = down, syr = c, modulusShifts = a} where
	c i = if m==0 then d else d*up + a!m where (d,m) = divMod i down
	a = listArray (1,down-1) [ 1 + div (up*r) down | r<-[1..down-1] ]

-- ist negativ, wenn man nur Zykel erwartet
estimate up down = (d-1)*log(fromIntegral up) - d*log d where d= fromIntegral down


-- Testet, ob eine Zahl in einem bekannten Zykel endet
tPos5_3 = t where
	s = syr $ createCollatz 5 3
	t i = if i == 4 || i == 8 then i else t $! s i

tNeg5_3 = t where
	s = syr $ createCollatz 5 3
	t i = if i== -1 then i else t $! s i


tPos7_5 = t where
	s = syr $ createCollatz 7 5
	t i = if i == 1 || i == 6 then i else t $! s i

tNeg7_5 = t where
	s = syr $ createCollatz 7 5
	t i = if i == -1 || i == -2 || i == -17 || i == -33 then i else t $! s i


tPos47_43 = t where
	s = syr $ createCollatz 47 43
	t i = if i == 1 || i == 281 then i else t $! s i

tNeg47_43 = t where
	s = syr $ createCollatz 47 43
	t i = if i >= -10 || i== -88 || i== -17140 then i else t $! s i


tPos385_379 = t where
	s = syr $ createCollatz 385 379
	t i = if i == 5 then i else t $! s i

tNeg385_379 = t where
	s = syr $ createCollatz 385 379
	t i = if i >= -63 then i else t $! s i




