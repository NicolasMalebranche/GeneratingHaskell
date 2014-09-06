{-# LANGUAGE TypeOperators, TypeFamilies #-}

-- Modul für Zusammenhangskoeffizienten der symmetrischen Gruppenalgebra
module ConnCoeffs where

import Partitions
import Data.Permute
import qualified Data.List as List

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
