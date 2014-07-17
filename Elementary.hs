module Elementary where
-- Elementare Funktionalität, die nicht vorimplementiert ist


-- Listenkombinationen
-- combinations [a,b,c..] = [[x,y,z..] | x<-a , y<-b, z<-c ..]
combinations :: [[a]] -> [[a]]
combinations [] = [[]]
combinations (l:r) = [a:b | a<-l , b<-combinations r]


-- Fakultätsfunktion
factorial = facAcc 1 where 
	facAcc a 0 = a
	facAcc a n = facAcc (n*a) (n-1)


-- Binomialkoeffizienten
binomial n k = if kk<0 then 0 else fromIntegral $ p 1 1 where
	kk = min k (n-k)
	p a i = if i>kk then a else p ((a*(n-kk+i))`div` i) (i+1)

-- Multinomialkoeffizienten
multinomial [] = 1
multinomial (m:r) = multinomial r * binomial (m+sum r) m 