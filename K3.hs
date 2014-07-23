module K3 
	where

import Data.Array
import Data.List
import Data.MemoTrie
import LinearAlgebra

type K3Domain = Int

-- Grad der Klassen einer K3 Fläche
degK3 :: (Num d) => K3Domain -> d
degK3 0 = 0 
degK3 23 = 4
degK3 i = if i>0 && i < 23 then 2 else error "Not a K3 index"

e8 = array ((1,1),(8,8)) $
	zip [(i,j) | i <- [1..8],j <-[1..8]] [
	-2, 1, 0, 0, 0, 0, 0, 0,
	1, -2, 1, 0, 0, 0, 0, 0,
	0, 1, -2, 1, 0, 0, 0, 0,
	0, 0, 1, -2, 1, 0, 0, 0,
	0, 0, 0, 1, -2, 1, 1, 0,
	0, 0, 0, 0, 1, -2, 0, 1,
	0, 0, 0, 0, 1, 0, -2, 0,
	0, 0, 0, 0, 0, 1, 0, -2 :: K3Domain]

inve8= array ((1,1),(8,8)) $
	zip [(i,j) | i <- [1..8],j <-[1..8]] [-2, -3, -4, -5, -6, -4, -3, -2, -3, -6, -8, -10, -12, -8, -6, -4,
		-4, -8, -12, -15, -18, -12, -9, -6, -5, -10, -15, -20, -24, -16, -12,
		-8, -6, -12, -18, -24, -30, -20, -15, -10, -4, -8, -12, -16, -20,
		-14, -10, -7, -3, -6, -9, -12, -15, -10, -8, -5, -2, -4, -6, -8,
		-10, -7, -5, -4 :: K3Domain]

-- BilinearForm auf K3 Flächen
bilK3_func ii jj = let 
	(i,j) = (min ii jj, max ii jj) 
	u 1 2 = 1
	u 2 1 = 1
	u 1 1 = 0
	u 2 2 = 0
	u i j = undefined	
	in
	if (i < 0) || (j > 23) then undefined else
	if (i == 0) then delta j 23 else
	if (i >= 1) && (j <= 2) then u i j else
	if (i >= 3) && (j <= 4) then u (i-2) (j-2) else
	if (i >= 5) && (j <= 6) then u (i-4) (j-4) else
	if (i >= 7) && (j <= 14) then e8 ! ((i-6), (j-6)) else
	if (i >= 15) && (j<= 22) then e8 ! ((i-14), (j-14))  else
	0 :: K3Domain

-- Inverse Bilinearform
bilK3inv_func ii jj = let 
	(i,j) = (min ii jj, max ii jj) 
	u 1 2 = 1
	u 2 1 = 1
	u 1 1 = 0
	u 2 2 = 0
	u i j = undefined	
	in
	if (i < 0) || (j > 23) then undefined else
	if (i == 0) then delta j 23 else
	if (i >= 1) && (j <= 2) then u i j else
	if (i >= 3) && (j <= 4) then u (i-2) (j-2) else
	if (i >= 5) && (j <= 6) then u (i-4) (j-4) else
	if (i >= 7) && (j <= 14) then inve8 ! ((i-6), (j-6)) else
	if (i >= 15) && (j<= 22) then inve8 ! ((i-14), (j-14))  else
	0 :: K3Domain

-- Cup Produkt mit zwei Faktoren
cup = memo2 r where
	r k (0,i) = delta k i
	r k (i,0) = delta k i
	r _ (i,23) = 0
	r _ (23,i) = 0
	r 23 (i,j) =  bilK3_func i j
	r _ _ = 0

-- Indizes, an denen das Cup Produkt nicht null ist
cupNonZeros = [ (k,(i,j)) | i<-[0..23],j<-[0..23], k<-[0..23], cup k (i,j) /= 0]

-- Cup Produkt mit beliebig vielen Faktoren
cupL = memo2 cL where
	cL k [] = delta 0 k
	cL k [i] = delta i k
	cL k [i,j] = cup k (i,j)
	cL k (i:r) = sum [cup k (i,j) * cupL j r | 
		(j,rr)<-cupLNonZeros (length r), rr == r]

-- Indexlisten, wo das Cupprodukt nicht (garantiert) null ist
cupLNonZeros :: (Integral i, HasTrie i) => i -> [(Int,[Int])]
cupLNonZeros = f where
	f = memo nz
	nz 0 = [(0,[])]
	nz n = [(k,i:r) | (k,(i,j)) <- cupNonZeros, (kk,r) <- f (n-1) , kk==j]

-- Adjungiertes zum Cup Produkt
cupAd = memo2 ad where 
	ad (i,j) k = sum [bilK3inv_func i ii * bilK3inv_func j jj 
		* cup kk (ii,jj) * bilK3_func kk k |(kk,(ii,jj)) <- cupNonZeros ]

-- Indizes, an denen das adjungierte Cup Produkt nicht null ist
cupAdNonZeros = [ ((i,j),k) | i<-[0..23],j<-[0..23], k<-[0..23], cupAd (i,j) k /= 0]

-- Adjungiertes Cup Produkt mit beliebig vielen Faktoren
cupAdL = memo2 cAL where
	cAL [] k = delta 23 k
	cAL [i] k= delta i k
	cAL [i,j] k = cupAd (i,j) k
	cAL (i:r) k = sum [cupAd (i,j) k * cupAdL r j | 
		(rr,j)<-cupAdLNonZeros (length r), rr == r]

-- Indexlisten, wo das adjungierte Cupprodukt nicht (garantiert) null ist
cupAdLNonZeros :: (Integral i, HasTrie i) => i -> [([Int],Int)]
cupAdLNonZeros = f where
	f = memo nz
	nz 0 = [([],23)]
	nz n = [(i:r,k) | ((i,j),k) <- cupAdNonZeros, (r,kk) <- f (n-1) , kk==j]

-- Eulerklasse
euler = array (0,23) [(i, cf i ) | i<-[0..23]] where
	cf l = sum [cup l (i,j) * cupAd (i,j) 0 | (k,(i,j)) <- cupNonZeros, k==l] 

interesting = array ((0,0),(23,23)) [ ((i,j), cupAd (i,j) 0) | i<-[0..23],j<-[0..23]]
