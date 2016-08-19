{-# LANGUAGE OverlappingInstances,
             FlexibleInstances,
             UndecidableInstances #-}

module ShowCoefficient where

import Data.Ratio

--  Stellt Zahlen als Koeffizienten dar

data CoefficientShow = ShowZero | ShowOne | ShowMinusOne | ShowJust String | ShowNegate String deriving Show

class ShowCoefficient a where
	showCoefficient :: a -> CoefficientShow


instance ShowCoefficient Rational where
   showCoefficient r = case (numerator r, denominator r) of
	(0,_) -> ShowZero
	(1,1) -> ShowOne
	(-1,1)-> ShowMinusOne
	(p,1) -> showCoefficient p
	(p,q) -> if p>0 then ShowJust $ [ c  | c <- show r , c/= ' '] ++ " "
		else ShowNegate $ [ c| c <- show $ -r , c/= ' ']++ " "

instance (Eq a, Show a, Num a) => ShowCoefficient a where
	showCoefficient r = case r of
		0 -> ShowZero
		1 -> ShowOne
		(-1)-> ShowMinusOne
		_ -> if signum r== -1 then ShowNegate$ show(-r) else ShowJust $ show r

{-

instance (ShowCoefficient a) => Show (PowerSeries a) where
	show r = let
		maxdeg = 20
		xpower i = if i == 0 then "" else if i== 1 then "t" else "t^" ++ show i
		showelem i a = case showCoefficient a of 
			ShowZero -> ""
			ShowOne -> if i==0 then "1" else " + " ++ xpower i
			ShowMinusOne ->  if i==0 then "-1" else " - " ++ xpower i
			ShowJust s -> if i==0 then s else " + "++ s ++xpower i
			ShowNegate s -> if i==0 then "-"++s else " - "++ s ++xpower i
		s i (Elem a r) = if i == maxdeg then " + O(" ++ xpower maxdeg ++ ")" else
			showelem i a ++ s (i+1) r
		in s 0 r
-}


