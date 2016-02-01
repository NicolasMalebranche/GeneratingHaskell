{-# LANGUAGE MultiParamTypeClasses, DeriveFunctor, FlexibleInstances #-}
import Prelude hiding (span,lines)
import Data.List hiding (span,lines)
import ShowMatrix
p = 3
mp = flip mod p

weil (a1,a2,a3,a4) (b1,b2,b3,b4) = mp (a1*b2 - b1*a2 + a3*b4 - b3*a4) 

bas = [ (a,b,c,d) | a <-[0..p-1], b<-[0..p-1], c<-[0..p-1], d<-[0..p-1] ]

instance Num (Integer,Integer,Integer,Integer) where
	(a1,a2,a3,a4)+(b1,b2,b3,b4) = (mp$a1+b2,mp$a2+b2,mp$a3+b3,mp$a4+b4)
	negate (a1,a2,a3,a4) = (mp$ -a1,mp$ -a2,mp$ -a3,mp$ -a4)
	fromInteger i = (i,i,i,i)

type Line = (Integer,Integer,Integer,Integer)
newtype Plane = Plane (Line,Line) deriving Show

instance Eq Plane where
	Plane(p1,q1) ==Plane(p2,q2) = span p1 q1 == span p2 q2

scale i (a,b,c,d) = (mp$i*a,mp$i*b,mp$i*c,mp$i*d)

-- 40 Ursprungsgeraden
lines = (0,0,0,1):[ (0,0,1,d) | d<-[0..p-1] ] ++[ (0,1,c,d) | c<-[0..p-1], d<-[0..p-1] ] ++ 
	[ (1,b,c,d) | b<-[0..p-1], c<-[0..p-1], d<-[0..p-1] ] :: [Line]

-- 130 Ebenen
planes :: [Plane]
planes = nub [Plane (l1,l2) | l1<-lines, l2<-lines, length ( span l1 l2) == fromInteger p^2]

degenerate (Plane (l1,l2)) = weil l1 l2 == 0

span x y = nub $ sort [ scale a x + scale b y | a<-[0..p-1],b<-[0..p-1]]

-- 81 nichtdegenerierte Ebenen (vs 49 degenerierte)
nodeg = [x | x<-planes , not $ degenerate x]

-- Shifts von nichtdegenerierten (insgesamt 675)
translates = nub [ sort [ v + w | v<- span x y ] | Plane (x,y) <- nodeg, w <- bas]  

-- Matrix (vom Rang 72)
oo = [ [ if any (b==) c then 1 else 0 |b<-bas] |c <- translates]

q = writeFile "Divisible3.txt" $ showGapMat2 oo
