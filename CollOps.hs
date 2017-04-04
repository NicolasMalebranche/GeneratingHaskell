module CollOps where

import Data.MemoTrie
import Data.List
import Data.Ratio

import SortBubble
import Table

data Ops = T Integer | B Integer deriving (Eq,Ord,Show)

baseB = 2
baseT = baseB + 1

applyOps n [] = n
applyOps n (T i:r) = applyOps (baseT*n + i) r
applyOps n (B i:r) = applyOps (baseB*n + i) r

numeric = applyOps 0

ruleB (B 0) = []
ruleB (B i) = [T (i + baseT-baseB)]

ruleT (T i) = if i<baseB then [B i] else ruleT (T d) ++ [B m] where
	(d,m) = divMod i baseB

compops (B i) (T j) = [T d, B m] where 
	(d,m) = divMod (baseT * i + j) baseB
compops a b = [a,b]

sortC = sortBubble compops


endOp [] = [] 
endOp(B i:r) = g (B i) (endOp r) where
	g x [] = ruleB x
	g x (t:r) = a: g b r where [a,b] = compops x t
	

eoi = memo e where
	e =  map f . endOp . map g 
	f (T i) = head $ show i
	g x = B $ read [x]

bs 0 = [0]
bs n = [ 10*x + i | x<-bs (n-1) , i <- [0..baseB-1] ]
ts 0 = [0]
ts n = [ 10*x + i | x<-ts (n-1) , i <- [0..baseB-1] ]

shortestEnd x = search 0 where
	search n = if f/=[] then last f else search (n+1) where 
		f = filter(\y -> x == eoi y) (map show $bs n)