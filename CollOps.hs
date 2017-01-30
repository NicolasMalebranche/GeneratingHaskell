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

data OpNums = T Int Integer | B Int Integer deriving (Eq,Ord,Show)

compress = f where
	f [] = []
	f (T0:r) = c (T 1 0) r
	f (T1:r) = c (T 1 1) r
	f (T2:r) = c (T 1 2) r
	f (B0:r) = c (B 1 0) r
	f (B1:r) = c (B 1 1) r
	c tb [] = [tb]
	c (T p n) (T0:b) = c (T (p+1) (3*n))  b
	c (T p n) (T1:b) = c (T (p+1) (3*n+1)) b
	c (T p n) (T2:b) = c (T (p+1) (3*n+2)) b
	c (T p n) (B0:b) = T p n: c (B 1 0) b
	c (T p n) (B1:b) = T p n: c (B 1 1) b
	c (B p n) (T0:b) = B p n: c (T 1 0) b
	c (B p n) (T1:b) = B p n: c (T 1 1) b
	c (B p n) (T2:b) = B p n: c (T 1 2) b
	c (B p n) (B0:b) = c (B (p+1) (2*n)) b
	c (B p n) (B1:b) = c (B (p+1) (2*n+1)) b



inflate [] = []
inflate (T p n:r) = dec p n ++ inflate r where
	t 0 = T0; t 1 = T1; t 2 = T2
	dec 0 _ = [] 
	dec p n = dec (p-1) d ++ [t m] where (d,m) = divMod n 3
inflate (B p n:r) = dec p n ++ inflate r where
	b 0 = B0; b 1 = B1
	dec 0 _ = [] 
	dec p n = dec (p-1) d ++ [b m] where (d,m) = divMod n 2
	
	
