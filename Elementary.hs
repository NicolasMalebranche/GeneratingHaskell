module Elementary where
-- Elementare Funktionalität, die nicht vorimplementiert ist


-- Listenkombinationen
-- combinations [a,b,c..] = [[x,y,z..] | x<-a , y<-b, z<-c ..]
combinations :: [[a]] -> [[a]]
combinations [] = [[]]
combinations (l:r) = [a:b | a<-l, b<-cr ] where cr=combinations r


-- Fakultätsfunktion
factorial n = fromIntegral $ facAcc n 1 where 
	facAcc 0 a = a
	facAcc n a = facAcc (n-1) $! n*a 

-- Pochhammer-Symbole
falling a = f where
	f n = if n==0 then 1 else (a-fromIntegral (n-1)) * f (n-1)
rising a = r  where
	r n = if n==0 then 1 else (a+fromIntegral (n-1)) * r (n-1)

-- Binomialkoeffizienten
binomial n k = if kk<0 then 0 else fromIntegral $ p 1 1 where
	kk = min k (n-k)
	p a i = if i>kk then a else p ((a*(n-kk+i))`div` i) (i+1)


-- Multinomialkoeffizienten
multinomial [] = 1
multinomial (m:r) = multinomial r * binomial (m+sum r) m 

-- Erweiterter Euklidischer Algorithmus
euclid 0 b = (b, (0, 1))
euclid a b = (gcd, (y - x*d, x)) where
	(d,m) = divMod b a
	(gcd, (x, y)) = euclid m a

-- Chinesischer Restsatz für [(Modulus, Rest)]
-- Die Moduli müssen paarweise teilerfremd sein
chinese l = snd $ foldr ch2 (1,0) l where
	ch2 (n,a) (n',b) = let
		(gcd, (x,y)) = euclid n n'
		r = x*b*n + y*a*n'
		kgv = n*n' `div` gcd
		in (kgv, mod r kgv)
