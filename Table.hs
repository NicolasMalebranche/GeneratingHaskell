module Table where

-- Funktionalitäten, um Listen zu sortieren und darzustellen

import Data.List


tableBy f l = [(fst $ head y, map snd y) | y <-g] where
	g=groupBy((.fst).(==).fst) $ sort [(f x,x)| x<-l]
	
printTable [] = return()
printTable((a,b):r) = let sa = show a in 
	foldl (>>) (putStrLn (sa ++ " : \t" ++ show (head b))) 
		[putStrLn (replicate (length sa +3) ' ' ++ '\t':show x)|  x <- tail b] 
			>> printTable r


