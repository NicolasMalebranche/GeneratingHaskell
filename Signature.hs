module Signature where

import Data.MemoTrie
import LinearAlgebra
import Data.Array.IO
import Data.PSQueue as PQ -- cabal install PSQueue-1.1
import qualified Data.List.Ordered as Asc
import qualified Data.IntMap as IM
import System.IO.Unsafe

ain = do 
	arr <- newArray (1,10) 37 :: IO (IOArray Int Int)
	a <- readArray arr 1
	writeArray arr 1 64
	mapWriteArray (+) arr [1,3,4,5,6,7]	
	b <- readArray arr 1 
	print (a,b)

mapWriteArray f ar = mw where
	mw [] = return ()
	mw (i:r) = do
		ae <- readArray ar i
		writeArray ar i (f ae i)
		mw r

gg _ = undefined :: IO (IOArray a b)

{-
signatur vs m = unsafePerformIO sig where
	mvs = map m vs
	-- Typ von m noch korrigieren!!
	pqstart = fromList $ zipWith ( :-> ) [1..] $ map IM.size mvs
	sparseLook i im = g $ IM.lookup i im where g Nothing = 0; g (Just x) = x
	inc x (a,b,c) = if x>0 then (a+1,b,c) else if x<0 then (a,b,c+1) else (a,b+1,c)
	sig = do 
		ar <- if False then gg 1 else newListArray (1,length vs) $ map IM.fromList mvs
		algo ar (0,0,0) (minView pqstart)
	algo ar = iter where
		iter acc Nothing = return acc
		iter acc (Just (k :-> _, pq)) = do
			kline <- readArray ar k
			let diag = sparseLook k kline
			-- if diag := 0 then
			let update pl p = IM.unionWith (-) pl $ IM.map (*(kline IM.!p/diag)) kline
			mapWriteArray update ar $ IM.keys kline
			let pqu = undefined
			iter (inc diag acc) $ minView pqu
-}

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

data Pivot a = Pi Int a | Bi Int Int a | Tri Int Int a a | Ignore

pivotStrategy ar pq = do
	(_,strat,npq) <- createStrat (minView pq) pq
	return (strat,npq)
	where
	sparseLook i im = g $ IM.lookup i im where g Nothing = 0; g (Just x) = x
	createStrat Nothing allpq = return (const True, undefined, undefined)
	createStrat (Just (k :-> kp, pq)) allpq= do
		kline <- readArray ar k
		let diag = sparseLook k kline
		if diag/=0 then return ((>)kp,Pi k diag, pq) else do
		-- Wenn das Diagonalelement gleich 0 ist
		(conseil,alterStrat,pq2) <- createStrat (minView pq) allpq
		bestM <- minSearch allpq Nothing $ IM.toList kline 
		if bestM==Nothing then return (const False,Ignore,pq) else do
		let Just (mp,mdiag,m,mv) = bestM
		let mstrat Nothing = Bi k m mv ;
			mstrat (Just x) = if x==0 then Bi k m mv else Tri k m x mv
		if conseil mp then 
			return ((>=) mp, mstrat mdiag, delete m pq) else 
			return (conseil,alterStrat,insert k mp pq2)
	minSearch pq acc [] = return acc
	minSearch pq acc ((j,jv):r) =  do
			let mjp = PQ.lookup j pq 
			if mjp == Nothing || jv==0 then minSearch pq acc r else do
			let Just jp = mjp
			jline <- readArray ar j
			let jdiag = IM.lookup j jline
			let np = if jdiag == Nothing then jp else jp+33456--kp 
			if acc == Nothing then minSearch pq (Just (np,jdiag,j,jv)) r else do
			let Just (mp,_,_,_) = acc
			if np < mp then minSearch pq (Just (np,jdiag,j,jv)) r else minSearch pq acc r

applyPivot ar pq = app where
	subtract _ pqu [] = return pqu
	subtract line pqu (i:r) = do
		ae <- readArray ar i
		let newline = IM.filterWithKey (\k v -> k/=i && v/=0) $ 
			IM.unionWith (-) ae $ line i
		let npqu = update (\_-> Just $ IM.size newline) i pqu		
		writeArray ar i newline
		subtract line npqu r
	app (Pi i diag) = do
		iline <- readArray ar i
		let line p = IM.map (*(iline IM.!p/diag)) iline
		subtract line pq $ IM.keys iline
	app (Bi i j ndia) = do
		iline <- readArray ar i
		jline <- readArray ar j
		let line p = IM.unionWith (+) (IM.map (*(jline IM.!p/ndia)) iline) 
			(IM.map (*(iline IM.!p/ndia)) jline)
		subtract line pq $ Asc.union (IM.keys iline) (IM.keys jline) 
	app (Tri i j diag ndia) = do
		iline <- readArray ar i
		jline <- readArray ar j
		let line p = IM.unionWith (+) (IM.map (*(jline IM.!p/ndia)) iline) $
			IM.unionWith (-) (IM.map (*(iline IM.!p/ndia)) jline)
				(IM.map (*(iline IM.!p*diag/ndia^2)) iline) 
		subtract line pq $ Asc.union (IM.keys iline) (IM.keys jline) 
	app Ignore = return pq

incPivot (a,b,c) = i where
	i (Pi _ v) = if v<0 then (a,b,c+1) else (a+1,b,c)
	i (Bi _ _ _) = (a+1,b,c+1)
	i (Tri _ _ _ _) = (a+1,b,c+1)
	i Ignore = (a,b+1,c)
	


