module PrimeFactors where

import Data.Numbers.Primes(primes)

-- Primfaktorzerlegung durch Ausprobieren.
-- Ergebnis ist Liste aus (Primzahl, Vielfachheit)
primeFactors  n = if n==0 then [] else trial primes $ abs n where
	trial (p:r) n = if n==1 then [] else if m==0 then up [p] d else trial r n where 
		(d,m) = divMod n p
		up ps n = if m==0 then up (p2:ps) d else down ps 1 n where p2 = head ps^2; (d,m) = divMod n p2
		down [] mu n = (p,mu-1) : trial r n
		down (p:r) mu n = if m==0 then down r (2*mu+1) d else down r (2*mu) n where (d,m) = divMod n p


