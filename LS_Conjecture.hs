{-# LANGUAGE GeneralizedNewtypeDeriving, ParallelListComp #-}
module LS_Conjecture
	where

import LS_Frobenius
import LS_Operators
import LS_Tor3 hiding(d)
import Elementary
import Data.Ratio

q = [([P(-1) (Tor 0)],1)]
d = [([Del],1)]
ad n u v = let
	r = ad (n-1) u v
	new = [ z | (x,a) <- r, (y,b) <- u, z<-[ (x++y,-a*b), (y++x,a*b) ]] 
	in if n==0 then v else sparseNub new
	
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
	a = Tor 0
	addel n = ad n d
	adq' = ad 1 $ ad 1 d q --[([L(-1) 0], -1)]
	leftO = adq' $ addel k $ [([P(-r) a],fromIntegral $ (r+1)^k)]
	rightO = addel k [([P(-r-1) a],fromIntegral $ (r-k)*(r)^k)]
	in multLists [sparseNub $ leftO++rightO] state
	--left = multLists [leftO] state
	--right = multLists [rightO] state
	--in putStrLn $ show left ++ "\n\n" ++ show (right `add` scale (-1) left)
