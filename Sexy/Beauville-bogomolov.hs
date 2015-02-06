
import HilbK3

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

