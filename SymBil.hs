module SymBil where


-- Berechnet das theta(d,k) aus
-- http://arxiv.org/abs/1507.00157

theta d k = let 
	binomial n k = product [ (n-i) | i <- [0..k-1]] `div` product [i | i<-[1..k]]
	a = product [ i ^ (d*binomial (k-i+d) d) | i<-[1..k]]
	beven = product [ i ^ binomial (k-i+d) d | i<-[1,3 .. 2*k+d-1]]
	bodd = product [ i ^ (binomial (k-i+d) d - binomial (k-2*i+d) d) | i<- [1.. k+ div (d-1) 2]]
	in if even d then a*beven else a*bodd

