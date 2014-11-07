module InfinitePolynomial where

import Data.List
import Partitions

listClean p = psrf where
	ps = sortBy ((.fst).compare.fst) p
	psr = map (\v -> (fst $ head v, sum $ map snd v)) $ groupBy ((.fst).(==).fst) ps 
	psrf = filter (\(g,a) -> a/=0) psr

-- Datenstruktur. Wird gespeichert als Sparse-Liste
newtype InfinitePolynomial p a = InfPol {list::[(p,a)]}

instance (Num a,Eq a, Partition p,Ord p) => Num (InfinitePolynomial p a) where
	fromInteger 0 = InfPol []
	fromInteger i = InfPol [(partEmpty,fromInteger i)]
	(InfPol a) + (InfPol b) = InfPol $ listClean $ a++b
	(InfPol a) * (InfPol b) = InfPol $ listClean [(partAdd p q, x*y)|(p,x)<-a,(q,y)<-b]
	negate (InfPol x) = InfPol $ map (\(p,a) -> (p,negate a)) x
	abs (InfPol x) = InfPol $ map (\(p,a) -> (p,abs a)) x
	signum (InfPol x) = InfPol $ map (\(p,a) -> (p,signum a)) x

instance (Num a, Eq a, Ord p) => Eq (InfinitePolynomial p a) where
	(InfPol a) == (InfPol b) = listClean a == listClean b

instance (Show a, Show p) => Show (InfinitePolynomial p a) where
	show (InfPol []) = "0"
	show (InfPol (s:x)) = showfst s ++ showrest x where
		showfst (p,a) = if sa == "1" then sp else if sa == "-1" then "-"++sp else 
			sa ++ sp where sa = show a; sp = show p
		showrest [] = ""
		showrest ((p,a):r) = (if head sa == '-' then " - "++un(tail sa) ++ show p else
			" + "++ un sa ++ show p) ++ showrest r where un "1" = "" ; un s = s; sa = show a