{-# LANGUAGE ScopedTypeVariables #-}
module MatrixRank where

import Data.MemoTrie
import System.IO.Unsafe
import System.Random
import LinearAlgebra
import BerlekampMassey

-- Berechnet den Rang der Matrix m nach der 1. Methode aus 
-- http://www.emis.de/journals/ELA/ela-articles/articles/vol11_pp16-23.ps
-- Probabilistische Methode mit Korrektheitsgarantie
-- vs1 sollte der Effizienz halber weniger Elemente enthalten als vs2
-- Funktioniert momentan nur mit diskreten Koerpern
rankCertificateUsingTrace vs1 vs2 a = run 0 where
	(n,m) = (length vs1, length vs2)
	random n _ = fromIntegral $ unsafePerformIO (getStdRandom (randomR (1,n))) 
	run 10 = error "Rank Algorithm unsuccesful"
	run i = if head polytail + trace vs1 b == 0 then rank else run (i+1) where
		d = memo $ random $ n^2
		b = memo2 $ \i j -> sum [a i k * d k * a j k | k <- vs2]
		v = memo $ random n
		wied = map (\x -> sum $ [x i * v i | i<-vs1]) bv where
			bv = v : map (\x -> vM vs1 x b) bv 
		polytail = tail (berle 2)  where 
			berle k = if length p*2 <= k then p else berle (k+2) where 
				p = berlekampMassey $ take k wied
		rank = length $ dropWhile (0==) $ reverse polytail

