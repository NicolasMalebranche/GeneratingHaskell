{-# LANGUAGE TypeOperators, TypeFamilies #-}

-- Modul für Zusammenhangskoeffizienten der symmetrischen Gruppenalgebra
module ConnCoeffs where

import Partitions
import Data.Permute
import qualified Data.List as List
import PowerSeries

compose s t = swapsPermute (max (size s) (size t)) (swaps s ++ swaps t)

-- c^mu_lambda,nu 
-- Auf wie viele Weisen läßt sich eine Permutation der Gestalt mu
-- als Produkt von Permutationen der Gestalt lambda, nu darstellen?
connCoeff mu lambda nu = length newperms where
	tau = partPermute mu
	piList = partAllPerms lambda
	nuAlpha = partAsAlpha nu
	newperms = filter ((==)nuAlpha.cycleType.compose tau) piList

-- Berechnet das Produkt von sum (partAllPerms lambda) mit
-- sum (partAllPerms nu). Gibt Liste aus (Partition,Vielfachheit)
connCoeffMultiply lambda nu = map f $ List.group $ List.sort list where
	pi = partPermute lambda
	pZL = partZ lambda
	list = map (cycleType.compose pi)(partAllPerms nu)
	f b@(mu:_) = (mu, (length b*partZ mu) `div` pZL )

-- Gibt Liste aus (Partition, Vielfachheit)
connCoeffDecompose mu lambda = map f $ List.group $ List.sort list where
	tau = partPermute mu
	list = map (cycleType.compose tau)(partAllPerms lambda)
	f b@(nu:_) = (nu,length b)

mymatrix mu lambda = sum x where
	par = partDegree mu + partDegree lambda - 4
	x = [ l | (nu,l) <- connCoeffDecompose mu lambda , partDegree nu == par]

writeM n = writeFile ("Conn4_"++show n++".txt") m where
	pp = partOfWeight n
	m = show [[mymatrix mu lambda | lambda <- pp] | mu <- pp] 
	
choose n k = ch1 n k where
	ch1 = ch
	ch 0 0 = 1
	ch n k = if n<0 || k<0 then 0 else if k> div n 2 + 1 then ch1 n (n-k) else
		ch1(n-1) k + ch1 (n-1) (k-1)
		
writeV n = writeFile ("Vec_"++show n++".txt") v where
	el vars = product [Elem 1 $ Elem x 0 | x<-vars]
	make vars = take n $ seriesToList $ sum [ fmap (choose x 2*) (el y)  | (x,y) <- dec vars]
	dec [a] = [(a,[])]
	dec (a:r) = (a,r) : [ (x,a:y) |(x,y)<-dec r]
	v = show [make vars | PartLambda vars <- map partAsLambda $ partOfWeight n]