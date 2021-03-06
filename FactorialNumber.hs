
module FactorialNumber where

import PAdic
import Elementary

-- Kempner-Funktion: kleinstes n>0, so daß n! `mod` k == 0
fnKempner k = if k==0 then 0 else fnK (abs k) 1  where
	fnK k n = if g == k then n else
		if g == 1 then fnK k (n+1) else fnK (div k g) (n+1) where 
		g = gcd n k 

-- [Primfaktorzerlegung von n! | n<-[0..]]
fnFactorialDec = [] : [] : run 2 (repeat []) (repeat []) where
	run p ([]:r) (a:ac) = ((toInteger p,1):a) : run (p+1) y z where
		g n = if n==0 then id else (:) (toInteger p,n)
		x = q $ map (1+) x
		q x = replicate (p-1) 0 ++ s : q t where
			s:t = x
		y = zipWith g (drop p x) r
		z = zipWith g (drop (p+1)$ scanl (+) 0 x) ac
	run p (x:r) (a:ac) = a : run (p+1) r ac

-- FN x == sum [ (i+1)! * x[i] | i<-[0..]]
-- Funktioniert auch mit unendlich langen Listen
newtype FactorialNumber = FN [Int] 

-- Korrigiert Digits, die nicht im vorgesehenen Bereich liegen
fnClean (FN x) = FN $ fc 1 0 x where
	fc i u (a:b) = m : fc (i+1) d b where (d,m) = divMod (a+u) i
	fc i 0 [] = []
	fc i u [] = fc i u [0]

-- Dasselbe mit Integer-wertigen Listen
fnClean' x = FN $ fc 1 0 x where 
	fc i u (a:b) = fromInteger m : fc (i+1) d b 
		where (d,m) = divMod (a+u) i
	fc i 0 [] = []
	fc i u [] = fc i u [0]

-- Zip-Funktion
fnZip f (FN x) (FN []) = FN $ map (flip f 0) x
fnZip f (FN []) (FN y) = FN $ map (f 0) y
fnZip f (FN (a:r)) (FN (b:q)) = FN $ f a b : z 
	where FN z = fnZip f (FN r) (FN q)

-- Wertet die Teilsummen aus. Konvergiert gegen die Zahl.
fnToSequence (FN x) = ts 0 1 1 x  where
	ts acc _ _ [] = repeat acc
	ts acc fac i (a:r) = nacc : ts nacc (fac*i) (i+1) r
		where nacc = acc + toInteger a*fac

-- Konvertiert in eine p-adische Zahl
fnToPAdic (FN x) = fp $ zipWith ((*).toInteger) x facs' where
	fp [] = 0
	fp y = Z_p a $ r + fp d where
		(t,d) = splitAt (p()) y
		Z_p a r = fromInteger $ sum t
	facs' = 1 : [ f*(if m==0 then d else i)| 
		(i,f)<-zip [1..] facs', let (d,m) = i `divMod` p()]

-- Eine mögliche Rückkonvertierung von einer p-adischen Zahl
-- fnToPAdic . fnFromPAdic = id
-- fnFromPAdic . fnToPAdic /= id
fnFromPAdic x = FN $ f 1 x where
	f n x = let
		(k,n') = orderRem_p n
		(a,b) = splitAtZ_p k x
		in a : f (n+1) (b*invZ_p n')

-- Interpretiert eine faktorielle Zahl als Lehmer-Code (rückwärts gelesen)
-- Terminiert, wenn eines von x und a endlich ist
-- x_i = # { j<i | a_j > a_i } 
fnPermute (FN x) a = f [] 0 x a where
	f l n [] a = l ++ a
	f l n x [] = l
	f l n (i:r) (a:b) = f (t ++ a:d) (n+1) r b where
		(t,d) = splitAt (n-i) $ l

-- Das ganze rückwärts. Konvergiert immer.
-- fnPermute (fnFromOrder x) x == sort x
fnFromOrder x = FN $ fO [] x where
	fO _ [] = []
	fO acc (a:r) = length [() | c<-acc, c>a] : fO (a:acc) r

-- Division mit Rest durch eine natürliche Zahl
fnDivMod fn@(FN x) k = (d , m) where 
	kk _ = fromIntegral k
	q = fnKempner $ kk(); qi = fromIntegral q
	fstC = product [1..q] `div` (kk())
	(d',m) = divMod (fnToSequence fn !! (qi-1)) $ kk()
	mults n p = p : mults (n+1) (p*(q+n) `div` n)
	r = zipWith ((*).fromIntegral) (drop qi x) $ mults 1 fstC
	d = fromIntegral d' + fnClean' r

-- Liefert diejenige Zahl x, so daß für alle p,n gilt:
-- x mod p^n = f p n 
-- fnChinese (const $ const x) = fromIntegral x
fnChinese f = FN $ make 1 $ tail fnFactorialDec where
	make fac (d:r) = fromIntegral q : make nfac r where
		nfac = product $ map fst l
		l = [ (p^m, f p m) | (p,m) <- d]
		q = chinese l `div` fac


-- Kann Gleichheit nur für endliche Zahlen entscheiden
instance Eq FactorialNumber where
	a==b = compare a b == EQ

instance Ord FactorialNumber where 
	compare (FN x) (FN y) = c x y where
		c (a:r) (b:q) = case compare a b of
			{EQ -> c r q;  other -> other}
		c (a:r) [] = if a>0 then GT else c r []
		c [] (b:q) = if b>0 then LT else c [] q
		c [][] = EQ

instance Num FactorialNumber where
	a@(FN x) * b@(FN y) = let
		e = zipWith ((*).toInteger) x $ fnToSequence b
		f = zipWith ((*).toInteger) y $ 0:fnToSequence a
		in fnClean' e + fnClean' f
	a + b = fnClean $ fnZip (+) a b
	a - b = fnClean $ fnZip (-) a b
	negate (FN x) = fnClean $ FN $ map negate x
	fromInteger n = FN $ fI 1 n where 
		fI i 0 = []
		fI i n = fromInteger m : fI (i+1) d where (d,m) = divMod n i
	abs = id
	signum = undefined

instance Show FactorialNumber where
	show (FN []) = "0"
	show (FN r) = init (ps 0 r "") ++ ".!" where
		maxDigits = 19
		sh i r = ((['0'..'9'] ++ ['a'..'z']) !! i) : r
		ps i [] a = a
		ps i (x:r) a = if i > maxDigits then ".."++a else ps (i+1) r (sh x a)