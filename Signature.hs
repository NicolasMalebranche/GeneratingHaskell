{-# LANGUAGE ScopedTypeVariables #-}
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

gg _ = undefined :: IO (IOArray Int b)
signature vs m = unsafePerformIO run where
	mvs = map m vs
	pqInit = fromList $ zipWith ( :-> ) [1..] $ map length mvs
	run = do
		ar <- if False then gg 1 else newListArray (1,length vs) $ map IM.fromList mvs
		iter ar pqInit (0,0,0)
	iter ar pq sig = if PQ.null pq then return sig else do
		(ps,npq) <- pivotStrategy ar pq 
		pr ps npq
		nnpq <- applyPivot ar npq ps
		pr ps nnpq
		iter ar nnpq (incPivot sig ps)
	pr (Pi i _) pq = print $ (findMin pq, PQ.lookup i pq)
	pr _ _ = return ()

data Pivot a = Pi Int a | Bi Int Int a | Ignore deriving (Show)

-- Eingabe: fun :: Index -> (Priorität, was anderes) und Queue
-- Ausgabe (neue Queue, min Index, was anderes am neuen Index)
trueMin fun pq = do 
		(fk,other) <- fun kk  
		mmin kk (fk,other) (insert kk fk pq) where
	Just (kk :-> kkp) = findMin pq
	mmin m (fm,om) pq = do
		let Just (k:->kp) = findMin pq
		if fm<=kp then return (pq,m,om) else do
		(fk,ok) <- fun k
		if fm<=fk then mmin m (fm,om) (insert k fk pq) else
			mmin k (fk,ok) (insert k fk pq)

-- Eingabe: Array und Queue von Indizes
-- Ausgabe: Strategie und aktualisierte Queue
-- Nur Lesezugriff auf das Array
pivotStrategy ar pq  = do
	(npq,k,strat) <- trueMin findStrat pq 
	print strat
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

-- Schreibt das Array gemäß den Pivot-Vorgaben
applyPivot ar pq strat = app strat where
	addLine line = al where
		al [] = return () 
		al (i:r) = do
			ae <- readArray ar i
			writeArray ar i $ IM.unionWith (+) ae $ line i
	killCols els mpq [] = return pq 
	killCols els mpq (i:rlist) = do
		ae <- readArray ar i
		let ce = IM.filter (\x -> abs x > 0.5^16) ae
		let e = List.foldr IM.delete ce els
		writeArray ar i e
		let npq = insert i (IM.size e) mpq
		killCols els npq rlist
	app (Pi i diag) = do
		iline <- readArray ar i
		let line p = IM.map (*negate (iline IM.!p/diag)) iline
		let list =  filter (\k-> k/=i) $ IM.keys iline
		addLine line list
		killCols [i] pq list
	app (Bi i j ndia) = do
		iline <- readArray ar i
		jline <- readArray ar j
		let line p = case (IM.lookup p jline,IM.lookup p iline) of
			(Just jx,Just ix) -> IM.unionWith (+) (IM.map (*negate(jx/ndia)) iline)
				(IM.map (*negate(ix/ndia)) jline)
			(Nothing,Just ix) -> IM.map (*negate(ix/ndia)) jline
			(Just jx,Nothing) -> IM.map (*negate(jx/ndia)) iline
		let list = filter (\k->k/=i&&k/=j) $ Asc.union (IM.keys iline)(IM.keys jline)
		addLine line list
		killCols [i,j] pq list
	app Ignore = return pq

incPivot (a,b,c) = i where
	i (Pi _ v) = if v<0 then (a,b,c+1) else (a+1,b,c)
	i (Bi _ _ _) = (a+1,b,c+1)
	i Ignore = (a,b+1,c)


