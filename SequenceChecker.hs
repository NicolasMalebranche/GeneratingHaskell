{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor, FunctionalDependencies, FlexibleInstances, ParallelListComp #-}
module SequenceChecker where

import PowerSeries
import LaurentSeries
import RationalFunction
import Polynomial
import ContinuedFraction
import Data.Ratio
import Data.IORef
import System.IO.Unsafe

checkerDegreeRef = unsafePerformIO $ newIORef 20
checkerDegreeRead _ = unsafePerformIO $ readIORef checkerDegreeRef 
checkerDegreeWrite = unsafePerformIO . writeIORef checkerDegreeRef 

data GeneratedByRat a = SeemsNot | SeemsToBe (RationalFunction a) deriving Show

-- Kettenbruchentwicklung einer Laurentreihe.
-- Die einzelnen Glieder haben alle höchstens Grad 0.
laurentCF l = floor : rest where
	rest = if trunc==0 then [] else laurentCF (recip trunc)
	trunc = laurentCutOrder 1 l
	floor = laurentCutDegree 1 l

-- Macht aus einer kettenbruchentwickelten Laurentreihe eine rationale Funktion
cfToRational = foldr resolve (1//0) where
	resolve (Lau d p) r = y + recip r where
		y = Rat (Polynomial (-d) p) (polyShift (-d) 1)

-- Checkt, ob Folge durch rationale Funktion erzeugt wird.
isRatGenerated seq = res where
	maxdeg = checkerDegreeRead ()
	cf = take (maxdeg+1) $ laurentCF $ Lau 0 $ seriesGenerating $ map fromIntegral seq
	rat = ratToIntegral $ ratReduce $ cfToRational cf
	res | length cf > maxdeg = SeemsNot
		| otherwise = SeemsToBe rat