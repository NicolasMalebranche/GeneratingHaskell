{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module LS_Hilb
	where

import Data.List
import Data.MemoTrie
import LS_Frobenius
import Partitions

data VertexOperator k = P Int k | L Int k | Del | C k deriving Show


onVak :: (Fractional a, Eq a, GradedFrobeniusAlgebra k) => [VertexOperator k] -> [([VertexOperator k],a)]

onVak [] = [([],1)]

onVak [P n k] = if n>=0 then [] else [([P n k],1)]
onVak [L _ _] = []
onVak [Del] = []
onVak [C k] = [([],1)]

onVak (p@(P n k) : r) = [ (t,y*x) | (q,x) <- onVak r, (t,y) <- pf q] where
	pf (p'@(P m k'): r) = if n<=m then [(p:p':r,1)] else 
		[(p':q',x) | (q',x) <- onVak (p:r)] ++ 
			if n+m==0 && x/=0 then [(r,x)] else [] where x=fromIntegral n * gfa_bilinear k k'