{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor  #-}
module DirichletSeries where

import Data.List
import Data.MemoTrie

data DirichletSeries a = Dirch {dirchCoeff :: Int -> a} deriving Functor

factorizations =  f where
	f n = half ++ root ++ map (\(a,b)->(b,a)) half where
		sq = round $ sqrt $ fromIntegral n
		sq2 = if sq^2 < n then sq else sq-1
		root = if sq^2 == n then [(sq,sq)] else []
		half = [(i,d)| i <- [1..sq2], let (d,m) = divMod n i, m==0]

-- Dirichlet Konvolution
dirchConvolution f g n = sum [f d * g k | (d,k) <- factorizations n]

-- Berechnet das Dirichlet-Inverse von f. Nimmt an, f 0 = 1
dirchInverseConst f = mi where
	mi = memo i
	i 1 = 1
	i n = negate $ sum [f d * mi k | (d,k) <- tail $ factorizations n]

-- Teilt g durch f. Nimmt an, f 0 = 1
dirchDivConst g f = mi where
	mi = memo i
	i 1 = g 1
	i n = g n - sum [f d * mi k | (d,k) <- tail $ factorizations n]

-- Eulersche phi-Funktion
eulerPhi = dirchDivConst id $ const 1

-- Moebius-Funktion
moebius = dirchInverseConst $ const 1

-- Dirichlet-Konvolution mit der Möbius-Funktion
moebiusInversion f n = sum [m k $ f d | (d,k) <- factorizations n] where
	m k = case moebius k of { 0 -> const 0; 1 -> id; -1 -> negate}

-- Differential einer Dirichlet Reihe
dirchDiff (Dirch f) = Dirch $ \ n -> f n * log (fromIntegral n)

-- Dirichletreihe der Mangoldt - Funktion
dirchMangold :: Floating a => DirichletSeries a
dirchMangold = negate $ dirchDiff zeta / zeta where zeta = Dirch $ const 1

instance (Eq a) => Eq (DirichletSeries a) where
instance (Num a) => Num (DirichletSeries a) where
	Dirch f + Dirch g = Dirch $ \n -> f n + g n
	Dirch f - Dirch g = Dirch $ \n -> f n - g n
	negate = fmap negate
	abs = undefined
	signum = undefined
	fromInteger i = Dirch $ \n -> if n==1 then fromInteger i else 0
	Dirch f * Dirch g = Dirch $ memo c where c = dirchConvolution f g

instance (Fractional a) => Fractional (DirichletSeries a) where
	Dirch g / Dirch f = Dirch mi where
		mi = memo i ; f1 = f 1
		i n = (g n - sum [f d * mi k | (d,k) <- tail $ factorizations n]) / f1
	fromRational a = Dirch $ \n -> if n==1 then fromRational a else 0


instance (Show a) => Show (DirichletSeries a) where
	show r = let
		maxdeg = 20
		xpower i = if i== 1 then "" else "/"++ show i++ "^s"
		showelem i a = if elem sa ["0","0.0","-0.0","0 % 1"] then "" else showsig ++ xpower i where
			sa = show a
			ska = if elem ' ' sa || elem '+' sa then "("++sa++")" else sa 
			showsig = if head ska == '-' then " - "++shown (tail ska) else " + "++shown ska
			shown a =  a
		s i r@(Dirch f) = if i == maxdeg then " + O(1" ++ xpower maxdeg ++ ")" else
			showelem i (f i) ++ s (i+1) r
		string = s 1 r 
		in (if string!!1 == '+'then "" else "-") ++  drop 3 string

