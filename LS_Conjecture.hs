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

adq m k state = let
	[kk,mm] =map fromIntegral [k,m]
	a = CP 0
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
	a = CP 0
	q = [([P(-1) 0],1)]
	adq' = ad 1 $ ad 1 d q 
	leftO = adq' $ ad k d $ [([P(-m) a],1%mm^k)]
	rightO = ad k d [([P(-m-1) a],(kk-mm)%(1+mm)^k)]
	fact = kk*(kk-1)*(kk-3*mm-2)%(1+mm)^(k-2) / 24
	diffO = ad (k-2) d  [([P(-1-m) c],fact*x*y) | (b,x) <- gfa_euler, (c,y) <- gfa_mult b a] 
	[left, right, diff] = [ multLists [o] state| o<- [leftO,rightO,diffO]]
	in putStrLn $ show left ++ "\n\n" ++ show (right `add` diff `add` scale (-1) left)


derQ m k state = let
	a = CP 1
	der = ad k [([Del],-1)] [([P(-m) a],1)]
	left = multLists [der] state
	r1 = scal (1% (fromIntegral k+1)) $ nor (k+1) m a
	--r2 ea = if k<2 then [] else  scal ((fromIntegral (m^2-1)*(-1)^k) % (fromIntegral (k-1) *12)) $ nor (k-1) m ea
	--r2e = [ (o,x*y*z) | (e,x) <- gfa_euler, (b,y) <- gfa_mult e a, (o,z) <- r2 b ]
	right = multLists [scal (fromIntegral m ^k) $ r1]state 
	in putStrLn $ show left ++ "\n\n" ++ show (right `add` scale (-1) left)


nor k m a = let 
	com = [sort c | c<- combinations $ replicate k $ [-10.. -1]++[1..3], sum c == -m]
	in sparseNub [ (o, x) | (l,x) <- gfa_comultN k a, c<-com,let o = zipWith P c l]



unor k m a = let
	com = [c | c<- combinations $ replicate k $ [-5.. -1]++[1], sum c == -m]
	in sparseNub [ (o, x) | (l,x) <- gfa_comultN k a, c<-com,let o = zipWith P c l]


