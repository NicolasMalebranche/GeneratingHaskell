{-# LANGUAGE ScopedTypeVariables #-}
module Zeckendorf where

import Data.MemoTrie
import Data.List

newtype ZeckendorfRepresentation = Zecken [Int]

instance Show ZeckendorfRepresentation where
	show (Zecken []) = "0"
	show (Zecken r) = concat $ intersperse " + " ["f_"++show i | i<-r]

fibonacci = memo f where
	f :: Int -> Integer	
	f 0 = 0
	f 1 = 1
	f n = fibonacci (n-1) + fibonacci (n-2)

goldenRatio = (1+ sqrt5) / 2 :: Double
sqrt5 = sqrt 5
logGoldenRatio = log goldenRatio

zecken 0 = Zecken []
zecken 1 = Zecken [2]
zecken 2 = Zecken [3]
zecken 3 = Zecken [4]
zecken n = let 
	m = ceiling $ log (fromIntegral n * sqrt5) / logGoldenRatio
	is = if fibonacci m > n then (m-1) else m
	Zecken r = zecken (n-fibonacci is)
	in Zecken $ is:r

fromZecken (Zecken r) = sum $ map fibonacci r

fibProduct x y = fromZecken $ zeckenProduct (zecken x) (zecken y) where
	zeckenProduct (Zecken a) (Zecken b) = Zecken [ i+j | i<-a, j<-b]
