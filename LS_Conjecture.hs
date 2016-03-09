{-# LANGUAGE GeneralizedNewtypeDeriving, ParallelListComp #-}
module LS_Conjecture
	where

import LS_Frobenius
import LS_Operators
import LS_Tor3
import Elementary
import Data.Ratio

conjecture s k state = let
	delFac i = scal (1%factorial i) . ad i [([Del],1)]
	qa = [([P(-1) $ Tor 1],1)]
	adqs = ad s [ ([P(-1)(Tor 0)],-1) ]	
	adq' = scal (1% ((s+1)^(k-s) *factorial s)) . ad s [ ([Del, P(-1) 0],1) , ([P(-1) 0, Del],-1)]
	left =multLists  [adqs $ delFac k qa] state
	right = multLists [delFac (k-s) $ adq' qa] state
	in putStrLn $ show left ++ "\n\n" ++ show right --(right `add` scale (-1) left)

der s k state = let
	a = Tor 1
	adqs = ad s [ ([P(-1)(Tor 0)],1) ]
	leftO = facDiff k $ P(-1-s) a
	rightO = scal (fromIntegral $(s+1)^k) $ adqs $ facDiff (s+k) $P(-1)a
	left = multLists [leftO] state
	right = multLists [rightO] state
	in putStrLn $ show left ++ "\n\n" ++ show (right `add` scale (-1) left)
