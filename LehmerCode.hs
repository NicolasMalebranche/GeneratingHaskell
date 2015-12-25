
module LehmerCode where

import Data.List

type LehmerCode = [Int]
type LehmerCodeReverse = [Int]


permuteFromLehmer :: LehmerCode -> [a] -> [a]
permuteFromLehmer [] _ = []
permuteFromLehmer _ [] = []
permuteFromLehmer (i:l) (a:r) = let
	(x,y) = splitAt i $ permuteFromLehmer l r 
	in x ++ a : y

-- L(s)_i = # { j | j > i, s_j < s_i } 
lehmerCode :: Ord a => [a] -> LehmerCode
lehmerCode [] = []
lehmerCode (a:r) = length [ () | b <- r, a > b] : lehmerCode r

-- entfernt einen Index aus dem Lehmer-Code
lehmerRemove :: Int -> LehmerCode -> LehmerCode
lehmerRemove i r = reverse $ rLehmerRemove (length r - i-1) $ reverse r


lehmerList :: Int -> [LehmerCode]
lehmerList i = if i<=1 then [[]] else [ j:r | j<-[0..i-1], r <- ll] where
	ll = lehmerList (i-1)


-- Funktioniert auch mit unendlichen Listen
rLehmerCode :: Ord a => [a] -> LehmerCodeReverse
rLehmerCode r = lc [] r where
	lc _ [] = []
	lc acc (a:r) = length [() | c<-acc, c>a] : lc (a:acc) r

-- entfernt einen Index aus dem Lehmer-Code
rLehmerRemove :: Int -> LehmerCodeReverse -> LehmerCodeReverse
rLehmerRemove i l = x ++ rem (drop 1 y) (head y) where
	(x,y) = splitAt i l 
	rem [] _ = []
	rem (j:r) h = if j > h then (j-1) : rem r h 
		else j : rem r (h+1) 