{-# LANGUAGE TypeFamilies, EmptyDataDecls, FlexibleContexts,
			 UndecidableInstances  #-}
module F_q where

import Data.Ratio
import PrimeFactors
import F_p hiding (con,decon)
import Polynomial


data Q4
newtype instance FQ Q4 = Q4 (Polynomial (F Mod2))
instance QExt Q4 where
	type QBase Q4 = Mod2
	con = Q4
	decon (Q4 i) = i
	irredPoly = const $ x^2 + x + 1

data Q8
newtype instance FQ Q8 = Q8 (Polynomial (F Mod2))
instance QExt Q8 where
	type QBase Q8 = Mod2
	con = Q8
	decon (Q8 i) = i
	irredPoly = const $ x^3 + x + 1

data Q16
newtype instance FQ Q16 = Q16 (Polynomial (F Mod2))
instance QExt Q16 where
	type QBase Q16 = Mod2
	con = Q16
	decon (Q16 i) = i
	irredPoly = const $ x^4 + x + 1

data Q9
newtype instance FQ Q9 = Q9 (Polynomial (F Mod3))
instance QExt Q9 where
	type QBase Q9 = Mod3
	con = Q9
	decon (Q9 i) = i
	irredPoly = const $ x^3 - x - 1

qFromPoly p = q where 
	q = con $ snd $ polyDivMod (fmap fromIntegral p) $ irredPoly q

data family FQ :: * -> *

class ModP (QBase a) => QExt a where
	type QBase a :: *
	irredPoly :: FQ a -> Polynomial (F (QBase a))
	con :: Polynomial (F (QBase a)) -> FQ a
	decon :: FQ a -> Polynomial (F (QBase a)) 



instance (QExt a) => Num (FQ a) where
	a + b = con (decon a + decon b)
	a - b = con (decon a - decon b)
	a * b = con $ snd $ polyDivMod (decon a * decon b) (irredPoly a)
	abs = undefined
	signum = undefined
	fromInteger i = con $ fromInteger i 

instance (QExt a) => Fractional (FQ a) where
	recip a = con $ ra where
		(_,(ra,_)) = polyEuclid (decon a) (irredPoly a)
	fromRational r = con $ polyConst $ fromRational r 

instance (QExt a) => Eq (FQ a) where
	 a == b = decon a == decon b

instance (QExt a) => Ord (FQ a) where
	compare a b = if a==b then EQ else 
		compare (polyToList $ decon a) (polyToList $ decon b)

instance (QExt a) => FiniteField (FQ a) where
	ffChar a = fromIntegral $ p $ head $polyToList $ decon a
	ffOrder a = ffChar a ^ deg (irredPoly a)
	ffAll = a where 
		n = deg $ irredPoly $ head a
		a = map (con.polyFromList) $ lis n
		lis 0 = [[]]
		lis n = [ s:r | r<-lis (n-1), s<-ffAll]
	primRoot = r where 
		r = check $ drop (ffChar r) ffAll
		phi =  ffOrder r - 1 
		divs = map (div phi . fst) (primeFactors phi) 
		check (r:t) = if all (/=1) [ r^e | e<-divs ] 
			then r else check t

instance (Show (Polynomial (F (QBase a))),QExt a) => Show (FQ a) where
	show x = show (decon x)
