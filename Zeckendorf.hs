module Zeckendorf where

import Data.MemoTrie
import Data.List
import Data.List.Ordered
import Data.Ratio

fibonacci = generalFib 0 1
	
lucas = generalFib 2 1

generalFib a b = gen where
	gen = memo g
	g :: Int -> Integer
	g 0 = a 
	g 1 = b
	g n = if n > 0 
		then gen (n-1) + gen (n-2)
		else gen (n+2) - gen (n+1)

goldenRatio = (1+ sqrt 5) / 2 :: Double
sqrt5 = sqrt 5
logGoldenRatio = log goldenRatio

-- Das Wythoff - Array
wythoff n m = zahl $ zeckenShift m q where
	q = zecken $ floor (fromIntegral n * goldenRatio^2) - 1

-- Darstellung ganzer Zahlen mit (Nega-)Fibonaccis
-- Die Liste muß aufsteigend sein
data Zeckendorf = Zecken {zeck::[Int], zeckNeg:: Bool } deriving (Eq,Ord)

zahl z = (if zeckNeg z then negate else id) $ sum [fibonacci i | i <- zeck z]
zeckApprox z = (if zeckNeg z then negate else id) $  
	sum [ goldenRatio ** (fromIntegral i) | i <- zeck z ]


zeckenShift shift (Zecken a n) = Zecken (map (shift +) a) n	

zecken n = Zecken (reverse $ z $ abs n) (n < 0) where 
	z 0 =  []
	z n = is : z (n-fibonacci is) where
		m = ceiling $ log (fromIntegral (abs n) * sqrt5) / logGoldenRatio
		is = if fibonacci m > n then (m-1) else m

negafib n = Zecken (z n) False where
	z 0 =  []
	z n = is : z (n-fibonacci is) where
		m = ceiling $ log (fromIntegral (abs n) * sqrt5) / logGoldenRatio
		is = if odd m == (n>0) then  - m else 1 - m

instance Num Zeckendorf where
	Zecken a n + Zecken b m  = case (a,b,n,m) of
		( [], _ , _ , _ ) -> Zecken b m
		( _ , [], _ , _ ) -> Zecken a n
		( _ , _ , False, False ) -> plus
		( _ , _ , False, True ) -> if numa<numb then negate minus else minus
		( _ , _ , True, False ) -> if numb<numa then negate minus else minus
		( _ , _ , True, True )  -> negate plus
		where
		shift = min (head a) (head b) - 4
		numa = sum [ fibonacci (i-shift) | i <- a]
		numb = sum [ fibonacci (i-shift) | i <- b]
		plus = zeckenShift shift $ zecken $ numa + numb
		minus = zeckenShift shift$ zecken $ abs $ numa - numb
	negate (Zecken a n) = Zecken a $ not n
	fromInteger = zeckMult 
	abs (Zecken a n) = Zecken a False
	signum (Zecken a n) = Zecken [0] n
	Zecken a n * Zecken b m = if (n==m) then mul else -mul where
		shift = head a + head b - 4
		mulz = [ fibonacci (i+j-shift) | i<-a, j<-b]
		mul = if mulz == [] then Zecken [] False 
			else zeckenShift shift $ zecken $ sum mulz
		
-- golden Ratio base
zeckMult 0 = Zecken [] False
zeckMult n = Zecken (zeck m) (n<0) where
	s = ceiling $ log (fromIntegral (abs n) * sqrt5) / logGoldenRatio + 1
	m = zeckenShift (-s) $ zecken $ abs n * fibonacci s
	
zeckMult1 = zeckenShift 1 . zeckMult

zeckToPair z =  (zahl $ zeckenShift (-1) z, zahl z)

zeckNorm z = a^2 + a*b - b^2 where
	(a,b) = zeckToPair z

zeckConj z = zeckMult (a+b) + zeckMult1 (-b) where 
	(a,b) = zeckToPair z

zeckQuotRem ab cd = let
	n = zeckNorm cd
	(a,b) = zeckToPair ab
	(c,d) = zeckToPair cd 
	(x,y) = (a*(c+d)-b*d, b*c-a*d)
	(m,l) = (round $ x%n, round $ y%n)
	q = zeckMult m + zeckMult1 l
	in if abs (zeckNorm ab) < abs n then (0,ab) else (q,ab-cd*q)
	
instance Real Zeckendorf
instance Enum Zeckendorf
instance Integral Zeckendorf where
	quotRem = zeckQuotRem
	toInteger = fst . zeckToPair

{-
zeckMult n = Zecken (if n == 0 then [] else list) (n<0) where
	t s = (zahl $ zeckenShift 1 $ zecken $ n*s) `mod` n == 0
	rep = head $ filter t [1..]
	[ r ] = zeck $ zecken rep
	list = map (+ (-r)) $ zeck $ zecken $ rep * n	
	
instance Show Zeckendorf where
	show = show . zahl

instance Num Zeckendorf where
	a+b = zeckenShift (sh-4) $ zecken $ zahl aa + zahl bb where
		[aa,bb] = map ( zeckenShift (4-sh) ) [a,b]
		sh = minimum $ map (foldr min 0 . zeck) [a,b]
	negate a = negafib $ negate $ zahl a -- sorry
	a*b = negafib $ zahl a * zahl b  -- sorry
	fromInteger = negafib 
	signum = negafib . signum . zahl 
	abs = zecken . abs . zahl
	
instance Real Zeckendorf where
	toRational = toRational . zahl
	
instance Enum Zeckendorf where
	fromEnum = fromEnum . zahl
	toEnum = zecken . toInteger

instance Integral Zeckendorf where
	toInteger = zahl
	divMod a b = (zecken x,zecken y) where (x,y) = divMod (zahl a) (zahl b)
	quotRem a b = (zecken x,zecken y) where (x,y) = quotRem (zahl a) (zahl b)
	


combs = alls :: [[Int]] where
	alls = inter 0 [[i] | i<-[0..]] [ (head x + n):x | (x,n)<- cantor alls [2..]]
	cantor (x:a) b = inter 0 [(x,y)|y<-b] $ cantor a b
	inter n (i:j) r = take n r ++ [i] ++ inter (n+1) j (drop n r)


	




infixl 8 +*

-- Fibonacci Product
(+*) x y = sum [ zeckenShift i y | i<-zeck x]

-- Was ganz was lustiges
istSpezialMod = let 
	range = map zecken [ 1 .. 100]
	in \n s -> all ( \r -> zahl (zecken (n*s) +* r - r) `mod` n == 0) range

spezialZahlenMod n = filter (istSpezialMod n)  [0..]

spezialNRange s = (unten,oben) where
	unten =  mun 2
	oben = run unten
	run n = if istSpezialMod n s then run (n+1) else n
	mun n = if istSpezialMod n s then n else mun (n+1)
-}

