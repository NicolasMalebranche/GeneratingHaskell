{-# LANGUAGE MultiParamTypeClasses, DeriveFunctor, FlexibleInstances,
	GeneralizedNewtypeDeriving #-}
import Prelude hiding (span,lines)
import Data.List hiding (span,lines)
import Data.Set
import ShowMatrix
import GroupAction

p = 3
-- p = 2
mp = flip mod p

weil (a1,a2,a3,a4) (b1,b2,b3,b4) = mp (a1*b4 - b1*a4 + a2*b3 - b2*a3) 

bas = [ (a,b,c,d)::Line | a <-[0..p-1], b<-[0..p-1], c<-[0..p-1], d<-[0..p-1] ]

instance Num (Integer,Integer,Integer,Integer) where
	(a1,a2,a3,a4)+(b1,b2,b3,b4) = (mp$a1+b1,mp$a2+b2,mp$a3+b3,mp$a4+b4)
	negate (a1,a2,a3,a4) = (mp$ -a1,mp$ -a2,mp$ -a3,mp$ -a4)
	fromInteger i = (i,i,i,i)

type Line = (Integer,Integer,Integer,Integer)
newtype Plane = Plane (Line,Line) deriving (Show,Ord)

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

-- 90 nichtdegenerierte Ebenen (vs 40 degenerierte)
nodeg = [x | x<-planes , not $ degenerate x]
degen = [x | x<-planes , degenerate x]

-- Shifts von nichtdegenerierten (insgesamt 810)
translates = nub [ sort [ v + w | v<- span x y ] | Plane (x,y) <- nodeg, w <- bas]  

-- Matrix (vom Rang 81)
oo = [ [ if any (b==) c then 1 else 0 |b<-bas] |c <- translates]

opi = [[ if any (b==) p then 1 else if any (b+t ==) p then -1 else 0 |b<-bas]  | Plane (a,aa) <- degen, let p = span a aa, t<- bas, t/=0 ]

q = writeFile "Divisible3.txt" $ showGapMat2 oo

-- Symplektische Gruppe
-- http://www.maths.usyd.edu.au/u/don/papers/genAC.pdf
data Sp4_2 = Sp4_2_A | Sp4_2_B deriving (Show, Eq, Enum) 
instance GroupAction Sp4_2 Line where
	gAct Sp4_2_A (a,b,c,d) = (mp$ a+c+d, mp$ a+d,mp$b+d,mp$a+b+c+d)
	gAct Sp4_2_B (a,b,c,d) = (c,a,d,b)

data Sp4_3 = Sp4_3_A | Sp4_3_B deriving (Show, Eq, Enum) 
instance GroupAction Sp4_3 Line where
	gAct Sp4_3_A (a,b,c,d) = (mp$2*a, b,c,mp$2*d)
	gAct Sp4_3_B (a,b,c,d) = (mp$a+c,a,mp$b+d,mp$ -b)

triples = nub [ fromList [x,y,-x-y] | x<-bas, y<-bas, x/=y, x/=0, y/=0]

