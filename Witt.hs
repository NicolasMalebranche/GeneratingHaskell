{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor #-}

-- Modul für Witt-Ringe
module Witt where

import PowerSeries

newtype WittUni x = WittUni (PowerSeries x) deriving Functor

wittUni seq = WittUni $ seriesShiftedProduct $ map (seriesConst . negate) seq

ghostUni (WittUni f) = let Elem _ r = f 
	in ordSequence $ Elem 0 $ negate $ seriesDiff (Elem 0 r) * seriesInvShift r

ghost p n = flip (!!) (p^n) . ghostUni 

witt p seq = wittUni $ w 1 0 seq where
	w pp 0 (a:s) = a : w (pp*p) (pp * (p-1) - 1 ) s 
	w _ _ [] = []
	w pp n seq = 0 : w pp (n-1) seq
	
 	
instance (Fractional a) => Num (WittUni a) where
	WittUni a + WittUni b = WittUni (a*b)
	WittUni a - WittUni (Elem _ r) = WittUni q where q = a - Elem 0 (q*r)
	x*y = WittUni e where e = seriesInt 1 (negate e*seriesShift (-1)(seriesGenerating(zipWith(*) (ghostUni x) (ghostUni y))))
	abs = undefined
	signum = undefined
	fromInteger = undefined