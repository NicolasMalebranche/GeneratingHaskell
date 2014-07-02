module K3 
	where

import Data.Array
import Data.List

delta :: (Num a) => Int -> Int -> a
delta i j = if i==j then 1 else 0

e8 = array ((1,1),(8,8)) $
	zip [(i,j) | i <- [1..8],j <-[1..8]] [
	-2, 1, 0, 0, 0, 0, 0, 0,
	1, -2, 1, 0, 0, 0, 0, 0,
	0, 1, -2, 1, 0, 0, 0, 0,
	0, 0, 1, -2, 1, 0, 0, 0,
	0, 0, 0, 1, -2, 1, 1, 0,
	0, 0, 0, 0, 1, -2, 0, 1,
	0, 0, 0, 0, 1, 0, -2, 0,
	0, 0, 0, 0, 0, 1, 0, -2]

inve8= array ((1,1),(8,8)) $
	zip [(i,j) | i <- [1..8],j <-[1..8]] [-2, -3, -4, -5, -6, -4, -3, -2, -3, -6, -8, -10, -12, -8, -6, -4,
		-4, -8, -12, -15, -18, -12, -9, -6, -5, -10, -15, -20, -24, -16, -12,
		-8, -6, -12, -18, -24, -30, -20, -15, -10, -4, -8, -12, -16, -20,
		-14, -10, -7, -3, -6, -9, -12, -15, -10, -8, -5, -2, -4, -6, -8,
		-10, -7, -5, -4]

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
	0

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
	0

cup k (ii,jj) = r (min ii jj) (max ii jj) where
	r 0 i = delta k i
	r i 23 = 0
	r i j = if k==23 then bilK3_func i j else 0

cupNonZeros = [ (k,(i,j)) | i<-[0..23],j<-[0..23], k<-[0..23], cup k (i,j) /= 0]

cupAd (i,j) k = sum [bilK3inv_func i ii * bilK3inv_func j jj * cup kk (ii,jj) * bilK3_func kk k |
	(kk,(ii,jj)) <- cupNonZeros ]

euler = array (0,23) [(i, cf i ) | i<-[0..23]] where
	cf l = sum [cup l (i,j) * cupAd (i,j) 0 | (k,(i,j)) <- cupNonZeros, k==l] 

interesting = array ((0,0),(23,23)) [ ((i,j), cupAd (i,j) 0) | i<-[0..23],j<-[0..23]]
