
module CyclotomicField where

import Polynomial
import PowerSeries
import PrimeFactors

cyclotomic n = run 1 1 (seriesGenerating [1,-1]) pf where
	pf = primeFactors n
	run deg s c [] = polyFromSeries (s*deg) $ seriesStretch s c
	run deg s c ((a,m):r) = run (deg*(a-1)) (s*a^(m-1)) newc r where
		newc = seriesStretch a c * seriesInv c
