module BerlekampMassey where

-- Berlekamp-Massey Algorithmus
-- Ausgabe: kuerzeste Folge c, fuer die gilt: 
-- all id $ zipWith (==) seq $ lfsr c (take (length c-1) seq)
berlekampMassey seq = run 0 [] seq 0 [1] 1 1 [1] where
	run _ _ [] _ c _ _ _  = c
	run i si (s:r) l c m b bB  = let
		d = s + sum (zipWith (*) si (tail c)) 
		newc = zipWithNull (-) c $ replicate m 0 ++ map ((d/b)*) bB
		next = run (i+1) (s:si) r
		in 	if d == 0 
			then next l c (m+1) b bB 
			else if 2*l <= i 
				then next (i+1-l) newc 1 d c 
				else next l newc (m+1) b bB 
	zipWithNull op = z where
		z (a:r) (b:s) = op a b : z r s
		z [] s = map (op 0) s
		z r [] = map (flip op 0) r


-- linear feedback shift register
lfsr c s_Init = let
	l = length reg; reg = tail c
	run st = s : run (s:init st) where s = negate $ sum $ zipWith (*) reg st
	in 	if length s_Init == l && head c ==1 
		then s_Init ++ run (reverse s_Init) 
		else error "Bad input" 

