module Zeckendorf where

import Data.MemoTrie
import Data.List

-- Darstellung ganzer Zahlen mit Nega-Fibonaccis
data Zeckendorf = Zecken {zahl::Integer, zeck::[Int]}

instance Show Zeckendorf where
	show = show . zahl

instance Num Zeckendorf where
	a+b = zecken $ zahl a + zahl b
	a-b = zecken $ zahl a - zahl b
	a*b = zecken $ zahl a * zahl b
	fromInteger = zecken 
	signum = signum . zecken . zahl 
	abs = abs . zecken . zahl
	
fibonacci = memo f where
	f :: Int -> Integer	
	f 0 = 0
	f 1 = 1
	f n = if n > 0 
		then fibonacci (n-1) + fibonacci (n-2)
		else fibonacci (n+2) - fibonacci (n+1)

goldenRatio = (1+ sqrt 5) / 2 :: Double


zecken = \ n -> Zecken n (z n) where
	sqrt5 = sqrt 5
	logGoldenRatio = log goldenRatio
	z 0 =  []
	z n = is : z (n-fibonacci is) where
		m = ceiling $ log (fromIntegral (abs n) * sqrt5) / logGoldenRatio
		is = if odd m == (n>0) then  - m else 1 - m
	
zeckenShift shift a = zecken $ sum $ map (fibonacci .( + shift )) $ zeck a

fibProduct x y = zecken $ sum [ fibonacci (i+j) | i<-zeck x, j<-zeck y]
