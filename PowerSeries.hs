{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor, FunctionalDependencies, MultiParamTypeClasses #-}
module PowerSeries where

import Data.List

infixl 5 °
class Composeable a b c | a b -> c where
	(°) :: a -> b -> c

data PowerSeries a = Elem a (PowerSeries a) 
	deriving (Functor)

-- das Monom t
t :: (Num a) => PowerSeries a
t = Elem 0 $ Elem 1 0

nullSeries _ = nll where
	nll = Elem 0 nll

-- Von Folge auf erzeugende Funktion
seriesGenerating (a:r) = Elem a $ seriesGenerating r
seriesGenerating [] = nullSeries ()

-- und zurück
ordSequence (Elem a r) = a : ordSequence r
expSequence :: Num a => PowerSeries a -> [a]
expSequence = makeexp 1 1 where
	makeexp i k (Elem a r) = (fromInteger k * a): makeexp (i+1) (i*k) r

seriesZip op = let 
	zz (Elem a r) (Elem b k) = Elem (op a b) $ zz r k
	in zz

seriesToList (Elem a r) = a:seriesToList r

seriesMult (Elem afst arst) = let
	f acc ale br = Elem (acc br) $ f newacc ar br where
		Elem a ar = ale
		newacc (Elem b rb) = a*b + acc rb
	facc (Elem b rb) = afst*b
	in f facc arst

seriesInv (Elem c r) = if c == 1 then seriesInvShift r else 
	error "Constant coefficient not 1"

-- Liefert 1/(1+x*r)
seriesInvShift r = inv where
	inv = Elem 1 invirr
	invirr = fmap negate $ seriesMult r inv

-- Setzt das x-Fache einer Reihe ein
seriesCompShift a r = co 1 a where
	co rpower (Elem a ar) = fmap (a*) rpower + Elem 0 (co (rpower*r) ar)

seriesComp a (Elem c r) = if c==0 then seriesCompShift a r else 
	error "Constant coefficient not 0"

seriesCompInv (Elem c (Elem l s)) = let
	b = Elem 1 r
	inv = Elem 0 b
	r = fmap negate $ seriesComp s inv * b^2
	in if (c,l) == (0,1) then inv else error "Not invertible"

seriesDiff (Elem s sr) = let
	d i (Elem a ar) = Elem (i*a) $ d (i+1) ar
	in d 1 sr

-- Setzt das negative Argument ein
seriesCompNegate (Elem s1 (Elem s2 s)) = Elem s1 $ Elem (negate s2) $ seriesCompNegate s

-- Multipliziert mit x^n. Falls n<0, killt die Terme mit negativen Exponenten.
seriesShift n s@(Elem _ ar) = if n < 0 then seriesShift (n+1) ar else
	if n == 0 then s else Elem 0 $ seriesShift (n-1) s

-- Schneidet oben ab. Reihe wird Polynom vom Grad n-1
seriesCutDegree n = ct 0 where 
	ct k (Elem a ar) = if k >= n then 0 else Elem a $ ct (k+1) ar

-- Schneidet unten ab. Reihe geht mit x^n los.
seriesCutOrder n = cb 0 where
	cb k (Elem a ar) = if k>=n then Elem a ar else Elem 0 $ cb (k+1) ar

instance (Num a) => Num (PowerSeries a) where
	(+) = seriesZip (+)
	(-) = seriesZip (-)
	negate = fmap negate
	abs = fmap abs
	signum = fmap signum
	fromInteger i = Elem (fromInteger i) (nullSeries ())
	(*) = seriesMult

instance (Fractional a) => Fractional (PowerSeries a) where
	recip (Elem c r) = let
		inv = Elem (recip c) invirr
		invirr = fmap negate $ seriesMult (fmap (/c) r) inv
		in inv
	fromRational a = Elem (fromRational a) (nullSeries ())

instance (Num a, Eq a) => Composeable (PowerSeries a)(PowerSeries a)(PowerSeries a) where
	(°) = seriesComp

seriesShiftedSum [] = 0
seriesShiftedSum (Elem a ar:r) = Elem a $ ar + seriesShiftedSum r

-- seriesShiftedProduct [a,b,..] = (1+a*x)(1+b*x^2)..
seriesShiftedProduct = ssp 1 1 1 where
	ssp acc t n [] = acc
	ssp (Elem a acc) t n (s:r) = 
		Elem a $ ssp (acc+st) (t+seriesShift n st) (n+1) r where st = s*t

-- Ganzzahlige bekannte Reihen
seriesCatalan :: Num a => PowerSeries a
seriesCatalan = Elem 1 $ seriesCatalan^2

seriesGeo :: Num a => PowerSeries a
seriesGeo = Elem 1 $ seriesGeo

-- Rationale bekannte Reihen
seriesExp ::  Fractional a => PowerSeries a
seriesCos ::  Fractional a => PowerSeries a
seriesSin ::  Fractional a => PowerSeries a
seriesAsin ::  Fractional a => PowerSeries a
seriesAtan ::  Fractional a => PowerSeries a
seriesLog :: Fractional a => PowerSeries a

seriesExp = fmap fromRational $ expmake 1 1 where
	expmake i k = Elem k $ expmake (i+1) (k/i)

seriesCos = fmap fromRational $ make 1 1 where
	make i k = Elem k $ Elem 0 $ make (i+2) (negate k/(i*i + i))
	
seriesSin = fmap fromRational $ Elem 0 $ make 2 1 where
	make i k = Elem k $ Elem 0 $ make (i+2) (negate k/(i*i + i))

seriesAsin = fmap fromRational $ arcsinMake 1 1 where
	arcsinMake i k = Elem 0 $ Elem (k/i) $ arcsinMake (i+2) (k*i/(i+1))

seriesAtan = fmap fromRational $ atanMake 1 where
	atanMake i = Elem 0 $ Elem (1/i) $ Elem 0 $ Elem (-1/(i+2)) $ atanMake (i+4)

seriesLog = fmap fromRational $ Elem 0 $ logmake 1 where 
	logmake i = Elem (1/i) $ Elem (-1/(i+1)) $ logmake (i+2)

seriesSqrt (Elem c s) = let
	r = fmap (/2) $ s - Elem 0 (r^2)
	rt = Elem 1 r
	in if c == 1 then rt else error "Constant Coefficient not 1"

instance Floating a => Floating (PowerSeries a) where
	pi = Elem pi 0
	exp (Elem c r) = fmap (*exp c) $ seriesCompShift seriesExp r
	log (Elem c r) = Elem (log c) x where
		Elem _ x = seriesCompShift seriesLog $ fmap (/c) r
	sin (Elem c r) = fmap (*sin c) (seriesCompShift seriesCos r) + 
		fmap (*cos c) (seriesCompShift seriesSin r)
	cos (Elem c r) = fmap (*cos c) (seriesCompShift seriesCos r) - 
		fmap (*sin c) (seriesCompShift seriesSin r) 
	sinh x = fmap (/2) $ exp x - exp (negate x)
	cosh x = fmap (/2) $ exp x + exp (negate x)
	asin x = atan $ x / sqrt (1-x^2)
	acos x = Elem (pi/2 - c) r where Elem c r = asin x
	atan (Elem c r) = Elem (atan c) x where
		Elem _ x = seriesCompShift seriesAtan $ r / (Elem (1+c^2) $ fmap (c*) r)
	asinh x = log $ x + sqrt (x^2+1)
	acosh x = log $ x + sqrt (x^2-1)
	atanh x = fmap (/2) $ log $ (1+x)/(1-x)
	sqrt (Elem c r) = fmap (* sqrt c) $ Elem 1 x where
		rr = fmap (/c) r
		x = fmap (/2) $ rr - Elem 0 (x^2)
	

tsch 0 = 1
tsch 1 = seriesGenerating [0,2]
tsch n = tsch 1* tsch(n-1) - tsch (n-2)



instance (Show a) => Show (PowerSeries a) where
	show r = let
		maxdeg = 20
		xpower i = if i == 0 then "" else if i== 1 then "t" else "t^" ++ show i
		showelem i a = if elem sa ["0","0.0","-0.0"] then "" else showsig ++ xpower i where
			sa = show a
			ska = if elem ' ' sa || elem '+' sa then "("++sa++")" else sa 
			showsig = if head ska == '-' then " - "++shown (tail ska) else " + "++shown ska
			shown a = if a=="1" || a=="1.0" then if i == 0 then "1" else "" else a
		s i (Elem a r) = if i == maxdeg then " + O(" ++ xpower maxdeg ++ ")" else
			showelem i a ++ s (i+1) r
		string = s 0 r 
		in (if string!!1 == '+'then "" else "-") ++  drop 3 string