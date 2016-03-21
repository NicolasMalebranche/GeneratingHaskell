{-# LANGUAGE GeneralizedNewtypeDeriving, ParallelListComp #-}
module LS_Conjecture
	where

import LS_Frobenius
import LS_Operators
import LS_Tor3 hiding(d)
import Elementary
import Data.Ratio
import Data.Ix
import Data.List
import SignedSort

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

lemma k r state = let
	a = P2 0
	q = [([P(-1) (P2 0)],1)]
	addel n = ad n d
	adq' = ad 1 $ ad 1 d q --[([L(-1) 0], -1)]
	leftO = adq' $ addel k $ [([P(-r) a],fromIntegral $ (r+1)^k)]
	rightO = addel k [([P(-r-1) a],fromIntegral $ (r-k)*(r)^k)]
	in multLists [sparseNub $ leftO++rightO] state
	--left = multLists [leftO] state
	--right = multLists [rightO] state
	--in putStrLn $ show left ++ "\n\n" ++ show (right `add` scale (-1) left)

adq m k state = let
	[kk,mm] =map fromIntegral [k,m]
	a = P2 0
	q = [([P(-1) 0],1)]
	leftO = ad 1 q $ ad (k+1) d [([P(-m) a],1)]
	left = scale (1%mm^(k+1)) $multLists [leftO] state
	rightO= ad k d  [([P(-1-m) a],1)]
	right = scale ( (kk+1)%(mm+1)^k) $ multLists [rightO] state
	diffO = ad (k-2) d [([P(-1-m) c],x*y) | (b,x) <- gfa_euler, (c,y) <- gfa_mult b a]
	diff =  scale ((kk+1)*(kk-1)*kk%(mm+1)^(k-2)/24) $ multLists [diffO] state
	in putStrLn $ show left ++ "\n\n" ++ show (right `add` diff `add` scale (-1) left)
	
adq' m k state = let
	[kk,mm] =map fromIntegral [k,m]
	a = P2 0
	q = [([P(-1) 0],1)]
	adq' = ad 1 $ ad 1 d q 
	leftO = adq' $ ad k d $ [([P(-m) a],1%mm^k)]
	rightO = ad k d [([P(-m-1) a],(kk-mm)%(1+mm)^k)]
	fact = kk*(kk-1)*(kk-3*mm-2)%(1+mm)^(k-2) / 24
	diffO = ad (k-2) d  [([P(-1-m) c],fact*x*y) | (b,x) <- gfa_euler, (c,y) <- gfa_mult b a] 
	[left, right, diff] = [ multLists [o] state| o<- [leftO,rightO,diffO]]
	in putStrLn $ show left ++ "\n\n" ++ show (right `add` diff `add` scale (-1) left)


derQ m k state = let
	a = P2 0
	der = ad k [([Del],-1)] [([P(-m) a],1)]
	left = multLists [der] state
	r1 = scal (1% (fromIntegral k+1)) $ nor (k+1) m a
	--r2 ea = if k<2 then [] else  scal ((fromIntegral (m^2-1)*(-1)^k) % (fromIntegral (k-1) *12)) $ nor (k-1) m ea
	--r2e = [ (o,x*y*z) | (e,x) <- gfa_euler, (b,y) <- gfa_mult e a, (o,z) <- r2 b ]
	right = multLists [scal (fromIntegral m ^k) $ r1]state 
	diffE = -- ad (k-2) [([Del],-1)]  [([P(-m) c],x*y)| (e,x) <-gfa_euler, (c,y) <-gfa_mult a e]
		concat [ scal (x*y/ (fromIntegral k+1)) $ ad 2 [([L 0 0],1)] $ nor (k-1) m c |(e,x) <-gfa_euler, (c,y) <-gfa_mult a e]
	diff = multLists [scal (fromIntegral ( m^2*(m-1)*(m+1))/24) diffE] state 
	diffE2 = -- ad (k-2) [([Del],-1)]  [([P(-m) c],x*y)| (e,x) <-gfa_euler, (c,y) <-gfa_mult a e]
		concat [ scal (x*y/ (fromIntegral k+1)) $ nor (k-1) m c |(e,x) <-gfa_euler, (c,y) <-gfa_mult a e]
	diff2 = multLists [scal (fromIntegral ( m^2*(m-1)*(m+1))/24) diffE2] state 
	in putStrLn $ {-show left ++ "\n\n" ++ -}show (right `add` scale (-1) left) ++ "\n\n" ++ show (diff) ++ "\n\n" ++ show diff2


nor k m a = let 
	com = [sort c | c<- combinations $ replicate k $ [-11.. -1]++[1..3], sum c == -m]
	in sparseNub [ (o, x) | (l,x) <- gfa_comultN (k-1) a, c<-com,let o = zipWith P c l]



unor k m a = let
	com = [c | c<- combinations $ replicate k $ [-6.. -1]++[], sum c == -m]
	in sparseNub [ (o, x) | (l,x) <- gfa_comultN (k-1) a, c<-com,let o = zipWith P c l]


