{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor, FlexibleInstances #-}

-- Modul für 2-adische Zahlen
module PAdicBin where

import System.IO.Unsafe
import Data.IORef
import Data.Ratio
import ContinuedFraction
import Data.Bits
import Data.Word
import Numeric

-- 2adische Zahlen, auf U64-Basis
data Z_Bin = Z64 Word64 Z_Bin

instance Show Z_Bin where
	show (Z64 u (Z64 v (Z64 w r))) = ".." ++ (if w==0 then "" else showHex w [] )++
		if v==0 && w==0 then showHex u []
		else showHex (toInteger v * 2^64 + toInteger u) []

scalarAdd :: Word64 -> Z_Bin -> Z_Bin
scalarAdd a (Z64 u s) = let
	r = a+u 
	in Z64 r $ if r < a.|.u then scalarAdd 1 s else s
	
-- "Skalarmultiplikation"
scalarMult :: Word64 -> Z_Bin -> Z_Bin
scalarMult sc = sma where
	-- Zerlegung in Blöcke der Länge 32
	a = sc .&. (2^32-1)
	b = sh sc
	sh = flip shiftR 32
	sma (Z64 u s) = let 
	  x = u .&. (2^32-1)
	  y = sh u
	  k1 = b*x + sh (a*x)
	  k2 = a*y
	  k12 = k1 + k2 
	  k = b*y + if k12 < k1 .|. k2 then sh k12 + 2^32 else sh k12
	  in Z64 (sc*u) $ scalarAdd k $ sma s
	  
-- liefert das Inverse modulo 2^64 für ungerade Eingaben
recipWord64 :: Word64 -> Word64
recipWord64 a = g 6 where
	g 0 = 1
	g i = let h = g (i-1) in (2-a*h)*h
		
instance Num Z_Bin where
	fromInteger i = Z64 (fromInteger i) $ fromInteger $ div i (2^64)
	(+) = add where
		add  (Z64 u s) (Z64 v t) = let r = u+v in
			Z64 r $ if r < u .|. v then add1 s t else add s t
		-- Summe + 1
		add1 (Z64 u s) (Z64 v t) = let r = u+v+1 in
			Z64 r $ if r <= u .|. v then add1 s t else add s t
	(-) = sub where
		sub  (Z64 u s) (Z64 v t) = let k = u-v in
			Z64 k $ if u < k .|. v then sub1 s t else sub s t
		sub1 (Z64 u s) (Z64 v t) = let k = u-v-1 in
			Z64 k $ if u <= k .|. v then sub1 s t else sub s t
	Z64 u s * y = Z64 v $ t + s*y where
		Z64 v t  = scalarMult u y 
		
instance Eq Z_Bin where
	Z64 u s == Z64 v t = u==v && s==t

instance Bits Z_Bin where
	Z64 u s .&. Z64 v t = Z64 (u .&. v) $ s .&. t
	Z64 u s .|. Z64 v t = Z64 (u .|. v) $ s .|. t
	Z64 u s `xor` Z64 v t = Z64 (u `xor` v) $ s `xor` t
	complement (Z64 u s) = Z64 (complement u) (complement s)
