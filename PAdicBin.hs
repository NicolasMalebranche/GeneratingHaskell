
-- Modul für 2-adische Zahlen
module PAdicBin where

import System.IO.Unsafe
import Data.IORef
import Data.Ratio
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
	ma = mult64Carry sc
	sma (Z64 u s) = Z64 (sc*u) $ scalarAdd (ma u) $ sma s

-- mult64Carry a b == c <=> a`mal`b == a*b + 2^64 c
-- 0 <= c < 2^64 - 1
mult64Carry :: Word64 -> Word64 -> Word64	  
mult64Carry a = ma where 
	sh = flip shiftR 32
	a1 = (2^32-1) .&. a
	a2 = sh a 
	ma b = let
		b1 = (2^32-1) .&. b
		b2 = sh b 
		k1 = a2*b1 + sh (a1*b1) 
		k2 = a1*b2
		k12 = k1 + k2
		in (if k12 < k1 .|. k2 then sh k12 + 2^32 else sh k12) + a2*b2
	
-- liefert das Inverse modulo 2^64 für ungerade Eingaben
recipWord64 :: Word64 -> Word64
recipWord64 a = g 7 1 where
	g 0 h = h
	g i h = g (i-1) $ (2-a*h)*h

-- multiplikatives Inverses für ungerade Eingaben
recipZ64 (Z64 a b) = aa where
	a_ = recipWord64 a
	c  = mult64Carry a a_
	aa = Z64 a_ $ (scalarAdd (-c) $ scalarMult (-a_) b) * aa
		
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
