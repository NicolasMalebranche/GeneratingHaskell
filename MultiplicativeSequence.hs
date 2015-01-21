module MultiplicativeSequence where

import Data.Ratio
import InfinitePolynomial
import Partitions
import PowerSeries

-- Ein paar Potenzreihen zu Standard multiplikativen Sequenzen
-------------------------------------------------------------------------------
chern :: PowerSeries Rational
chern = seriesGenerating [1,1]

pontr :: PowerSeries Rational
pontr = seriesGenerating [1,0,1]

segre :: PowerSeries Rational
segre = seriesGenerating $ repeat 1

todd :: PowerSeries Rational
todd = recip $ seriesCompNegate x where Elem _ x = seriesExp

hirzeL :: PowerSeries Rational
hirzeL = sq $ c / s where 
	sq (Elem a (Elem _ r)) = Elem a $ sq r
	Elem _ s = seriesExp - en ; c = seriesExp + en
	en = seriesCompNegate seriesExp

ahat :: PowerSeries Rational
ahat = cr 1 $ recip $ fmap (/2) $ s where
	Elem _ s = seriesExp - seriesCompNegate seriesExp
	cr k (Elem a (Elem _ r)) = Elem (a/k) $ cr (4*k) r
-------------------------------------------------------------------------------

instance (Fractional a,Eq a, Partition p,Ord p,Show p) => 
	Fractional (InfinitePolynomial p a) where
	fromRational r = InfPol [(partEmpty,fromRational r)]
	(/) = undefined

linearTrafo (Elem a x) z@(Elem b y) = let q = if a==0 then 0 else a/b in 
	q : linearTrafo (x-fmap (*q) y) (seriesDiff z)

applyTrafo (q:p) z = let Elem a x = fmap (*q) z in
	Elem a $ x + applyTrafo p (seriesDiff z)

-- stellt die Potenzreihe des ersten Arguments in Polynomen der des zweiten dar
multiplicativeTrafo (Elem _ f) (Elem _ g) = let
	Elem _ lf = seriesCompShift seriesLog f
	Elem _ lg = seriesCompShift seriesLog g
	a = map fromRational $ linearTrafo lf lg
	ref = seriesGenerating [ InfPol [(PartLambda [i],1%1)] | i<-[1..]]
	Elem _ lref = seriesCompShift seriesLog ref
	ltr = applyTrafo a lref
	in seriesCompShift seriesExp ltr

-- leitet die Potenzreihe des ersten Arguments nach dem k-ten Element der zweiten ab
multiplicativeDiff (Elem _ f) (Elem _ g) k =  let
	Elem _ lf = seriesCompShift seriesLog f
	Elem _ lg = seriesCompShift seriesLog g
	a = map fromRational $ linearTrafo lf lg
	b = map fromRational $ linearTrafo lg lf
	ref = seriesGenerating [ InfPol [(PartLambda [i],1%1)] | i<-[1..]]
	Elem _ lref = seriesCompShift seriesLog ref
	ltr = negate $ applyTrafo b lref
	ee = seriesShift k $ seriesCompShift seriesExp ltr
	in applyTrafo a ee * Elem 1 ref
