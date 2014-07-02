
import LinearAlgebra
import SequenceChecker
import PowerSeries
import MatrixAlgorithms
import Data.Ratio
import Polynomial
import RationalFunction

fac n = product [1..n]
m:: Int -> Int -> Integer
--m = defm [[1,0,-3,-7],[2,1,0,6],[5,2,-6,-5],[1,-1,-1,1]]
m1 = defm [[1,-1,4,7],[0,1,-1,-1],[0,0,1,0],[0,0,0,1]]
m2 = defm [[1,0,0,0],[4,1,0,0],[-5,-3,1,0],[9,2,-5,1]]
m = mM vs m1 m2
vs = [0..3]
powers = delta : map (mM vs m) powers
s = [trace vs m | m<-powers]

charPos = [berkowitz vs m | m <- powers]
coeffs n = map (!!n) charPos

ch = polyFromList $ reverse $ berkowitz vs m
dch = polyDiff ch

trp = polyReverse dch // polyReverse ch

sprung n (a:b) = a: sprung n (drop (n-1) b)

