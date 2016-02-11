module PrimeFactors where

import Data.Numbers.Primes(primes)

-- Primfaktorzerlegung durch Ausprobieren.
-- Ergebnis ist Liste aus (Primzahl, Vielfachheit)
primeFactors n = if n==0 then [] else trial (bound n) primes $ abs n where
	bound n = ceiling $ sqrt $ (fromIntegral n :: Double)
	trial b (p:r) n = if p>b then if n/=1 then [(n,1)] else [] else 
		case divide n p 0 of
		(_,0) -> trial b r n
		(nn,m) -> (p,m) : trial (bound nn) r nn 
	divide n s mult = case divMod n s of
		(d,0) -> divide d s (mult+1)
		_ -> (n,mult) 
