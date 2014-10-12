module Signature(
	signature
	) where

import Data.MemoTrie
import Data.Maybe
import Data.Array.IO
import Data.PSQueue as PQ -- cabal install PSQueue-1.1
import qualified Data.List.Ordered as Asc
import qualified Data.IntMap as IM
import qualified Data.List as List
import System.IO.Unsafe

gg _ = undefined :: IO (IOArray a b)
signature vs m = unsafePerformIO run where
	mvs = map m vs
	pqInit = fromList $ zipWith ( :-> ) [1..] $ map length mvs
	run = do
		ar <- if False then gg 1 else newListArray (1,length vs) $ map IM.fromList mvs
		iter ar pqInit (0,0,0)
	iter ar pq sig = if PQ.null pq then return sig else do
		(ps,npq) <- pivotStrategy ar pq 
		nnpq <- applyPivot ar npq ps
		iter ar nnpq (incPivot sig ps)

data Pivot a = Pi Int a | Bi Int Int a | Ignore deriving (Show)

trueMin fun pq = do 
		(fk,other) <- fun k  
		mmin k (fk,other) (insert k fk pq) where
	Just (k :-> kp) = findMin pq
	mmin m (fm,om) pq = do
		let Just (k:->kp) = findMin pq
		if fm<=kp then return (pq,m,om) else do
		(fk,ok) <- fun k
		if fm<=fk then mmin m (fm,om) (insert k fk pq) else
			mmin k (fk,ok) (insert k fk pq)

pivotStrategy ar pq  = do
	(npq,k,strat) <- trueMin findStrat pq 
	return (strat, rem strat (delete k npq)) where
	rem (Bi _ j _) = delete j
	rem _ = id
	findStrat j = do
		jline <-readArray ar j
		let diag = IM.lookup j jline
		let Just jp = PQ.lookup j pq 
		if IM.null jline then return (0,Ignore) else 
			if isNothing diag then pivot2 j jline else 
				return (jp,Pi j $ fromJust diag) 
	pivot2 j jline = do 
		diags <- diagFilter $ map fst $ IM.toList jline
		let (vm,m) = minimum $ zip (map val diags) diags
		if List.null diags then 
			return (val(fst$IM.findMin jline)+1,undefined) else 
			return (val m, Bi j m $ jline IM.! m)
	val i = fromJust $ PQ.lookup i pq
	diagFilter [] = return []
	diagFilter (i:r) = do 
		iline <- readArray ar i 
		dfr <- diagFilter r
		return $ if IM.member i iline then dfr else i:dfr

applyPivot ar pq = app where
	subtract _ pqu [] = return pqu
	subtract line pqu (i:r) = do
		ae <- readArray ar i
		let newline = IM.filterWithKey (\k v -> v/=0) $ 
			IM.unionWith (+) ae $ line i
		let npqu = update (\_-> Just $ IM.size newline) i pqu
		writeArray ar i newline
		subtract line npqu r
	app (Pi i diag) = do
		iline <- readArray ar i
		let line p = IM.map (*negate (iline IM.!p/diag)) iline
		subtract line pq $ IM.keys iline
	app (Bi i j ndia) = do
		iline <- readArray ar i
		jline <- readArray ar j
		let line p = case (IM.lookup p jline,IM.lookup p iline) of
			(Just jx,Just ix) -> IM.unionWith (+) (IM.map (*negate(jx/ndia)) iline)
				(IM.map (*negate(ix/ndia)) jline)
			(Nothing,Just ix) -> IM.map (*negate(ix/ndia)) jline
			(Just jx,Nothing) -> IM.map (*negate(jx/ndia)) iline
		subtract line pq $ Asc.union (IM.keys iline) (IM.keys jline) 
	app Ignore = return pq

incPivot (a,b,c) = i where
	i (Pi _ v) = if v<0 then (a,b,c+1) else (a+1,b,c)
	i (Bi _ _ _) = (a+1,b,c+1)
	i Ignore = (a,b+1,c)


