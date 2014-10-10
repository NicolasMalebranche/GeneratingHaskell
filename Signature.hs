module Signature(signatur) where

import Data.MemoTrie
import LinearAlgebra
import Data.Array.IO
import Data.PSQueue
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

signatur vs m = unsafePerformIO sig where
	mvs = map m vs
	-- Typ von m noch korrigieren!!
	pqstart = fromList $ zipWith ( :-> ) [1..] $ map IM.size mvs
	sparseLook i im = g $ IM.lookup i im where g Nothing = 0; g (Just x) = x
	inc x (a,b,c) = if x>0 then (a+1,b,c) else if x<0 then (a,b,c+1) else (a,b+1,c)
	sig = do 
		ar <- if False then gg 1 else newListArray (1,length vs) mvs
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


data Pivot a = Pi Int a | Bi Int Int a 

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

	


-- Signatur einer symmetrischen Matrix: (positive, null, negative) Eigenwerte
-- Der Koeffizientenbereich muss ein Koerper sein, um gigantische Zahlen zu vermeiden 
-- www.cas.mcmaster.ca/~cs777/presentations/voicu.pdf 
signature vs m = if el1/=0 then alg1 v1 else 
	if el2/=0 then alg2 v2 else (0,fromIntegral $ length vs,0) where 
	(el1,v1) = piv1 [] vs; (el2,v2) = piv2 [] vs 
	piv1 acc [] = (0, acc)
	piv1 acc (i:r) = if el /= 0 then (el, i:acc++r) else piv1 (i:acc) r where el = m i i
	alg1 (i:r) = if el1 < 0 then (a,b,c+1) else (a+1,b,c) where
		(a,b,c) = signature r mm 
		mi = memo (m i)
		mm p q = m p q - mi p * mi q / el1
	piv2 acc [] = (0,acc)
	piv2 acc (i:r) = p [] r where
		p a2 [] = piv2 (i:acc) r
		p a2 (j:s) = if el/=0 then (el,i:j:acc++a2++s) else p (j:a2) s where el = m j i
	alg2 (i:j:r) = (a+1,b,c+1) where
		(a,b,c) = signature r mm
		mi = memo (m i); mj = memo (m j)
		mm p q =  m p q - (mi p * mj q + mi q * mj p) / el2

