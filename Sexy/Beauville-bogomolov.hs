
import HilbK3
import K3
import Partitions

-- Beauville-Bogomolov Form via Cup-product
bb n = [round $ qu i j - qus i - qus j | i<-h, j<-h]  where
	qus a = reduce $ cupIntList $ replicate (2*n) a	
	qu a b = reduce $ makeInt $ ci $ cL $ 2*n where
		cL 1 = sparseNub $ intCrea b ++ intCrea a
		cL k = x where
			cLr = cL (k-1)
			ib = intCrea b
			ia = intCrea a
			x = sparseNub $ [(e,v*w*fromIntegral z) | 
				(p,v) <- cLr, let m = multAn p, (q,w) <- ib, (e,z)<-m q] ++
				[(e,v*w*fromIntegral z) | (p,v) <- cLr, let m = multAn p, (q,w) <- ia, (e,z)<-m q] 
		makeInt l = [(e,toInt z) | (e,z) <- l]
		ci l = sparseNub [(s,v*fromIntegral w) | (e,v) <- l, (s,w) <- creaInt e]
	reduce [(_,i)] =  c* fromIntegral(signum i)*(fromIntegral (abs i) **(1/fromIntegral n)) 
	reduce [] = 0
	c = (fromIntegral $ product [n+1..2*n] )**(-1/fromIntegral n)
	h = hilbBase n 2

bB :: AnBase -> AnBase -> Int
bB (PartLambda (1:s), (i:ir)) (PartLambda (1:t), (j:jr)) = 
	if s==t && all (==0) ir && all (==0) jr then bilK3 i j else 0
bB (PartLambda (2:s), nl) (PartLambda (2:t),ml) =
	if all (==0) nl && all (==0) ml && all (==1) s && s==t then -2*(length s+1) else 0
bB _ _ = 0



ind2 bil (a,b) (c,d) = ab*cd + ac*bd + ad*bc where
	[ab,ac,ad,bc,bd,cd] = zipWith bil [a,a,a,b,b,c] [b,c,d,c,d,d]

ind3 bil (a,b,c) (d,e,f) = ab*(cd*ef+ce*df+cf*de) + ac*(bd*ef+be*df+bf*de)+ ad*(bc*ef+be*cf+bf*ce) + ae*(bc*df+bd*cf+cd*bf) + af*(bc*de+bd*ce+be*cd)  where
	[ad,ae,af,bd,be,bf,cd,ce,cf]= zipWith bil [a,a,a,b,b,b,c,c,c]$ cycle [d,e,f]
	[ab,ac,bc,de,df,ef] = zipWith bil [a,a,b,d,d,e][b,c,c,e,f,f]

sym3 [] = []
sym3 t@(a:r) = [(a,b,c) | (b,c) <- sym2 t] ++ sym3 r
sym2 [] = []
sym2 t@(a:r) = [(a,b) | b<-t] ++ sym2 r

pairpartitions [] = [[]]
pairpartitions (a:r) = [(a,b):y | (b,x) <- take1 [] r, y<-pairpartitions x] where
	take1 v (x:h)  = (x,v++h) : take1 (v++[x]) h
	take1 _ [] = []

compForm = [r | x<- sym3 (hilbBase 3 2), let r = (ind3 bB x x, cupup x) , r/=(0,0)] where
	cupup (a,b,c) = sum $map snd $ cupIntList [a,a,b,b,c,c]

h = hilbBase 4 4
red [] = 0
red [(_,i)] = i
t x = cupIntList $ replicate 4 x
