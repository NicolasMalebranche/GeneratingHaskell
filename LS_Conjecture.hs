{-# LANGUAGE GeneralizedNewtypeDeriving, ParallelListComp #-}
module LS_Conjecture
	where

import LS_Frobenius
import LS_Operators
import LS_Tor3 hiding(d)
import Elementary
import Data.Ratio
import Data.Ix

newtype CPDomain = CP Int deriving (Show,Eq,Ord,Ix,Num)
instance GradedFrobeniusAlgebra CPDomain where
	gfa_deg (CP 0) = -2
	gfa_deg (CP 1) = 0
	gfa_deg (CP 2) = 2
	
	gfa_1 = [(0,1)]
	gfa_K = []
	
	gfa_T (CP 2) = -1
	gfa_T _ = 0
	
	gfa_base = [0,1,2]
	gfa_baseOfDeg 0 = [1]
	gfa_baseOfDeg (-2) = [0]
	gfa_baseOfDeg 2 = [2]
	gfa_baseOfDeg _ = []
	
	gfa_mult (CP 0) i = [(i,1)]
	gfa_mult i (CP 0) = [(i,1)]
	gfa_mult (CP 2) _ = []
	gfa_mult _ (CP 2) = []
	gfa_mult (CP 1) (CP j) =  [(2, 1)]

	gfa_bilinearInverse i =  [(2-i, -1)]
	

q = [([P(-1) (Tor 0)],1)]
d = [([Del],1)]
{-ad n u v = let
	r = ad (n-1) u v
	new = [ z | (x,a) <- r, (y,b) <- u, z<-[ (x++y,-a*b), (y++x,a*b) ]] 
	in if n==0 then v else sparseNub new
-}	
conjecture s k state = let
	delFac i = scal (1%factorial i) . ad i [([Del],1)]
	qa = [([P(-1) $ Tor 1],1)]
	adqs = ad s [ ([P(-1)(Tor 0)],-1) ]	
	adq' = scal (1% ((s+1)^(k-s) *factorial s)) . ad s [ ([Del, P(-1) 0],1) , ([P(-1) 0, Del],-1)]
	left =multLists  [adqs $ delFac k qa] state
	right = multLists [delFac (k-s) $ adq' qa] state
	in putStrLn $ show left ++ "\n\n" ++ show right --(right `add` scale (-1) left)

der s k state = let
	e = 3
	a = Tor 1
	adqs = ad s [ ([P(-1)(Tor 0)],1) ]
	leftO = facDiff k $ P(-e-s) a
	rightO = scal (fromIntegral ((s+e)^k) % fromIntegral e^(s+k)) $ adqs $ facDiff (s+k) $P(-e)a
	left = multLists [leftO] state
	right = multLists [rightO] state
	in putStrLn $ show left ++ "\n\n" ++ show (right `add` scale (-1) left)

lemma k r state = let
	a = CP 0
	q = [([P(-1) (CP 0)],1)]
	addel n = ad n d
	adq' = ad 1 $ ad 1 d q --[([L(-1) 0], -1)]
	leftO = adq' $ addel k $ [([P(-r) a],fromIntegral $ (r+1)^k)]
	rightO = addel k [([P(-r-1) a],fromIntegral $ (r-k)*(r)^k)]
	in multLists [sparseNub $ leftO++rightO] state
	--left = multLists [leftO] state
	--right = multLists [rightO] state
	--in putStrLn $ show left ++ "\n\n" ++ show (right `add` scale (-1) left)

thm m n o k l i state = let
	a = Tor 0
	b = 0
	norm n k a = scal (1 % fromIntegral n^k) $ facDiff k $P(-n) a
	x = norm m k a
	y = norm n l a
	u = norm o i a
	z = norm (n+m-o) (k+l-i) a
	left  =  multLists [ad 1 x y] state
	right = multLists [ad 1 u z] state
	in putStrLn $ show left ++ "\n\n" ++ show right --(right `add` scale (-1) left)

