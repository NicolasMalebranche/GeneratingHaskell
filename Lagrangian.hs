{-# LANGUAGE MultiParamTypeClasses, DeriveFunctor, FlexibleInstances,
	GeneralizedNewtypeDeriving, TypeFamilies #-}

module Lagrangian where

import Prelude hiding (span,lines)
import Data.List hiding (span,lines)
import Data.Set hiding (map,filter,foldr)
import ShowMatrix
import GroupAction
import F_p
import SymplecticGroup
import Data.AdditiveGroup
import Data.VectorSpace

dim = 4
type Coeff = F Mod3
instance AdditiveGroup Coeff where
	zeroV = 0
	(^+^) = (+)
	negateV = negate
allCoeffs = [0..] :: [Coeff]


newtype Vect = Vect [Coeff] deriving (Show,Eq,Ord)
collinear v w = w==zeroV || any (v==) [s*^w | s<- allCoeffs]
allVectors = map Vect $ a dim where 
	a 0 = [[]] 
	a n = [c:v | v <- a (n-1), c<-allCoeffs ]
instance AdditiveGroup Vect where
	zeroV = Vect $ replicate dim 0
	Vect a ^+^ Vect b = Vect $ zipWith (+) a b
	negateV (Vect a) = Vect $ map negate a
instance VectorSpace Vect where
	type Scalar Vect = Coeff
	s *^ Vect a = Vect $ map (s*) a
instance InnerSpace Vect where
	Vect a <.> Vect b = symplecticForm a b 
instance GroupAction Sp Vect where
	gAct g (Vect v) = Vect $ gAct g v

	
newtype Line = Line Vect deriving (Show,Eq,Ord)
normalizeLine (Line (Vect v)) = Line $ s v *^ Vect v where
	s [] = 1; s(x:y) = if x/=0 then recip x else s y
genLine v = normalizeLine (Line v)
allLines = toAscList $ fromList $ map genLine $ filter (zeroV/=) allVectors
spanLine (Line l) = [s*^l | s<-allCoeffs]
instance GroupAction Sp Line where
	gAct g (Line l) = genLine $ gAct g l


newtype Plane = Plane (Vect,Vect) deriving (Show,Eq,Ord)
spanPlane (Plane (a,b)) = toAscList $ fromList [s*^a ^+^ t*^b | s<-allCoeffs, t<-allCoeffs]
normalizePlane p = fir $ spanPlane p where
	fir (v:r) = if v/=zeroV then sec r else fir r where
		sec (w:r) = if collinear v w then sec r else Plane (v,w)
genPlane a b = normalizePlane $ Plane (a,b)
allPlanes = toAscList $ fromList [genPlane a b | Line a <- allLines, 
	Line b <- allLines, not $ collinear a b]
isDegenerate (Plane (a,b)) = a <.> b == 0
nondegPlanes = filter (not. isDegenerate) allPlanes
orthogonalPlane (Plane (a,b)) = fir allLines where 
	fir (Line v:r) = if a <.> v ==0  && b<.> v==0 then sec r else fir r where
		sec (Line w:r) = if a <.> w ==0  && b<.> w==0 && not (collinear v w) then 
			genPlane v w else sec r
instance GroupAction Sp Plane where
	gAct g (Plane (a,b)) = genPlane (gAct g a) (gAct g b)

planeTranslates = [x| p<-nondegPlanes, let ps = spanPlane p, 
	x<-toAscList$fromList [ map (^+^ v) ps | v <- spanPlane $ orthogonalPlane p] ]

planeSpanSum = [ [if any (b==) ps then 1 else 0 | b<-allVectors]| p<-nondegPlanes , let ps = spanPlane p]
writePlaneSpanSum = writeFile "PlaneSpanSum.txt" $ showGapMat2 planeSpanSum

planeSpanIdeal = [ [if any (b==) pt then 1 else 0 | b<-allVectors]| pt<-planeTranslates ]
writePlaneSpanIdeal = writeFile "PlaneSpanIdeal.txt" $ showGapMat2 planeSpanIdeal

planeSpanShift = [ [if any (b==) ps then -1 else if any ((b^-^t)==) ps then 1 else 0 | b<-allVectors]| 
	p<-nondegPlanes, let ps = spanPlane p, t <- spanPlane $ orthogonalPlane p, t/=zeroV]
writeSpanShift = writeFile "PlaneSpanShift.txt" $ showGapMat2 planeSpanShift

classP = (sym e e, p) where
	p@(Plane(a,b)) = head nondegPlanes
	e = ext a b

sparseNub [] = []
sparseNub l = sn (head sl) (tail sl) where
	sl = sortBy ((.fst).compare.fst) l
	sn (i,x) ((j,y):r) = if i==j then sn (i,x+y) r else app (i,x) $ sn (j,y) r
	sn ix [] = app ix []
	app (i,x) r = if x==0 then r else (i,x) : r
instance Num [(Vect,Coeff)] where
	a+b = sparseNub $ a++b
	a*b = sparseNub [ (x ^+^ y,i*j) | (x,i)<-a,(y,j) <-b]
	negate a = [ (x,negate i) | (x,i)<-a]
	fromInteger i = [ (Vect [0,0,0,0],fromInteger i)]

toLong element = [case x of {Just (_,i) -> i::Coeff; _ ->0}| b<-allVectors, let x = find ((b==).fst) element]
fromPlane p= [(t,1::Coeff)| t<-spanPlane p]

generatesD = [
	Plane(Vect[1,0,0,0],Vect[0,1,0,0]), --  8
	Plane(Vect[1,0,0,0],Vect[0,1,0,1]), -- +4
	Plane(Vect[1,0,0,0],Vect[0,1,0,2]), -- +1
	Plane(Vect[1,0,0,0],Vect[0,1,1,1]), -- +2
	Plane(Vect[1,0,0,1],Vect[0,1,2,1]), -- +4
	Plane(Vect[1,0,1,1],Vect[0,1,0,1]), -- +2
	Plane(Vect[1,0,1,0],Vect[0,1,0,1]), -- +2
	Plane(Vect[1,0,1,1],Vect[0,1,2,2]),
	Plane(Vect[0,0,1,0],Vect[0,0,0,1]) 
	]


maxIdeal =  [ [(v,1::Coeff)]+(-1)  | v<-tail allVectors]
planeD = [ toLong $ a*m | a<-map fromPlane generatesD, m<-maxIdeal]
writeD = writeFile "PlaneD.txt" $ showGapMat2 planeD


generatesD' = [ x*([(v,1)]-1)| let p = Plane(Vect[1,0,0,0],Vect[0,1,0,0]), let pT = orthogonalPlane p, let x = fromPlane p, v<- tail $ spanPlane pT]
	++ [  x*([(v,1)]-1) | let p= Plane(Vect[0,0,1,0],Vect[0,0,0,1]), let pT = orthogonalPlane p, let x = fromPlane p, v<- drop 2 $ spanPlane pT]
	++ [  x*([(v,1)]-1) | let x= fromPlane$ Plane(Vect[1,0,0,0],Vect[0,1,0,1]), v<-map Vect [[0,0,0,1],[2,0,1,2],[1,0,2,0],[1,0,2,1] ] ]
	++ [ fromPlane (Plane(Vect[1,0,0,0],Vect[0,1,0,2])) * ([(v,1)]-1) | let v = Vect [1,0,1,0] ]
	++ [ fromPlane (Plane(Vect[1,0,0,0],Vect[0,1,1,1])) * ([(v,1)]-1) | v <- map Vect [[0,0,1,1],[1,0,0,1]] ]
	++ [ fromPlane (Plane(Vect[1,0,0,1],Vect[0,1,2,1])) * ([(v,1)]-1) | v <- map Vect [[0,1,1,2],[1,0,0,2], [1,1,1,1], [2,2,2,2]] ]
	++ [ fromPlane (Plane(Vect[1,0,1,1],Vect[0,1,0,1])) * ([(v,1)]-1) | v <- map Vect [[0,1,0,2],[1,0,2,2]] ]
	++ [ fromPlane (Plane(Vect[1,0,1,0],Vect[0,1,0,1])) * ([(v,1)]-1) | v <- map Vect [[0,1,0,2],[1,0,2,0]] ]
	++ [ fromPlane (Plane(Vect[1,0,1,1],Vect[0,1,2,2])) * ([(v,1)]-1) | v <- map Vect [[1,1,0,2]] ]

planeD' = map toLong generatesD'
writeD' = writeFile "PlaneD'.txt" $ showGapMat2 planeD'

planeBig = [ toLong $ a*m | a<-map fromPlane allPlanes, m<-maxIdeal]
writeBig = writeFile "PlaneBig.txt" $ showGapMat2 planeBig


instance GroupAction Sp (Sym,Plane) where
	gAct g (x,y) = (gAct g x, gAct g y)

	
-- == O aus dem Paper
symplClass = toList $ gOrbit [SpR,SpJ,SpD] classP


sumSpan = [ x++[if any (b==) (map (t^+^) ps) then 1 else 0 | b<-allVectors] | (Sym x,p)<-symplClass, 
	let ps =(spanPlane p), t<-spanPlane (orthogonalPlane p) ]
writeSumSpan = writeFile "SumSpan.txt" $ showGapMat2 sumSpan

superSpan = [ x++[if any (b==) ps then -1 else if any ((b^-^t)==) ps then 1 else 0 | b<-allVectors] | (Sym x,p)<-symplClass, 
	let ps =(spanPlane p), t<-spanPlane (orthogonalPlane p), t/= zeroV ]
writeSuperSpan = writeFile "SuperSpan.txt" $ showGapMat2 superSpan

dimExt = (dim*(dim-1)) `div` 2
newtype Ext = Ext [Coeff] deriving (Show,Eq,Ord)
instance AdditiveGroup Ext where
	zeroV = Ext $ replicate dimExt 0
	Ext a ^+^ Ext b = Ext $ zipWith (+) a b
	negateV (Ext a) = Ext $ map negate a
instance VectorSpace Ext where
	type Scalar Ext = Coeff
	s *^ Ext a = Ext $ map (s*) a
ext (Vect a) (Vect b) = Ext [a!!i * b!!j - a!!j * b!!i | i<-[0..dim-1],j<-[i+1..dim-1]]
allExt= map Ext $ a dimExt where 
	a 0 = [[]] 
	a n = [c:v | v <- a (n-1), c<-allCoeffs ]
instance GroupAction Sp Ext where
	gAct g = f where 
		e = [gAct g $ Vect [if i==j then 1 else 0 | i<- [1..dim]]| j<-[1..dim]]
		le = [ ext (e!!i)(e!!j) | i<-[0..dim-1],j<-[i+1..dim-1]]
		f (Ext v) = foldr (^+^) zeroV $ zipWith (*^) v le
		
dimSym = (dimExt*(dimExt+1)) `div` 2
newtype Sym = Sym [Coeff] deriving (Show,Eq,Ord)
instance AdditiveGroup Sym where
	zeroV = Sym $ replicate dimSym 0
	Sym a ^+^ Sym b = Sym $ zipWith (+) a b
	negateV (Sym a) = Sym $ map negate a
instance VectorSpace Sym where
	type Scalar Sym = Coeff
	s *^ Sym a = Sym $ map (s*) a
sym (Ext a) (Ext b) = Sym [a!!i * b!!j + if i/=j then a!!j * b!!i else 0
	| i<-[0..dimExt-1],j<-[i..dimExt-1]]
instance GroupAction Sp Sym where
	gAct g = f where 
		gac = gAct g
		e = [gac $ Ext [if i==j then 1 else 0 | i<- [1..dimExt]]| j<-[1..dimExt]]
		le = [ sym (e!!i)(e!!j) | i<-[0..dimExt-1],j<-[i..dimExt-1]]
		f (Sym v) = foldr (^+^) zeroV $ zipWith (*^) v le
