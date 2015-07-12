module KroneckerSymbol
(kroneckerSymbol, jacobiSymbol) where

-- Kronecker- und Jacobi-Symbol aus der Zahlentheorie

kroneckerSymbol a 0 = if a == 1 || a == -1 then 1 else 0
kroneckerSymbol a n = f $ ks a (abs n) where
	f = if n<0 && a<0 then negate else id

jacobiSymbol a n = let
	jsOdd a 1 = 1
	jsOdd 0 n = 0
	jsOdd 1 n = 1
	jsOdd a n = mod8 n ^ e * mod4 a n * jsOdd (mod n r) r  where (r,e) = killEvens a
	mod4 a n = if mod a 4 == 3 && mod n 4 == 3 then -1 else 1
	in 
	if n<0 || even n then error "Jacobi symbol undefined" 
	else fromIntegral (jsOdd (mod a n) n :: Int)

ks a n = if odd n then jacobiSymbol a n else oddify a n where
	oddify a n = if even a then 0 else
		mod8 a ^ e * jacobiSymbol a nr where (nr,e) = killEvens n

-- wichtige mod8 -Funktion
mod8 n = case mod n 8 of { 1 -> 1; 3 -> -1; 5 -> -1; 7 -> 1; _ -> 0}

-- Ungerader Teil einer Zahl
killEvens k = if m == 1 then (k,0) else (r,e+1) where
	(d,m) = divMod k 2
	(r,e) = killEvens d