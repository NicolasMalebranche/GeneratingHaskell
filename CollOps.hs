module CollOps where

import SortBubble

data Ops = T0 | T2 | T1 | B0 | B1 deriving (Eq,Ord,Show,Enum)


numeric = nu 0 where
	nu n [] = n
	nu n (T0:r) = nu (3*n) r
	nu n (T1:r) = nu (3*n+1) r
	nu n (T2:r) = nu (3*n+2) r
	nu n (B0:r) = nu (2*n) r
	nu n (B1:r) = nu (2*n+1) r

compops B0 T0 = [T0,B0]
compops B0 T1 = [T0,B1]
compops B0 T2 = [T1,B0]
compops B1 T0 = [T1,B1]
compops B1 T1 = [T2,B0]
compops B1 T2 = [T2,B1]
compops a b  = [a,b]

sortC =  sortBubble compops

data OpNums = T Integer | B Integer deriving (Eq,Ord,Show)

compress = f where
	f [] = []
	f (T0:r) = c (T 0) r
	f (T1:r) = c (T 1) r
	f (T2:r) = c (T 2) r
	f (B0:r) = c (B 0) r
	f (B1:r) = c (B 1) r
	c tb [] = [tb]
	c (T n) (T0:b) = c (T $ 3*n  ) b
	c (T n) (T1:b) = c (T $ 3*n+1) b
	c (T n) (T2:b) = c (T $ 3*n+2) b
	c (T n) (B0:b) = T n: c (B 0) b
	c (T n) (B1:b) = T n: c (B 1) b
	c (B n) (T0:b) = B n: c (T 0) b
	c (B n) (T1:b) = B n: c (T 1) b
	c (B n) (T2:b) = B n: c (T 2) b
	c (B n) (B0:b) = c (B $ 2*n  ) b
	c (B n) (B1:b) = c (B $ 2*n+1) b



inflate [] = []
inflate (T 0:r) = T0 : inflate r
inflate (T n:r) = dec n ++ inflate r where
	t 0 = T0; t 1 = T1; t 2 = T2
	dec 0 = [] 
	dec n = dec d ++ [t m] where (d,m) = divMod n 3
inflate (B 0:r) = B0 : inflate r
inflate (B n:r) = dec n ++ inflate r where
	b 0 = B0; b 1 = B1
	dec 0 = [] 
	dec n = dec d ++ [b m] where (d,m) = divMod n 2
	
	
