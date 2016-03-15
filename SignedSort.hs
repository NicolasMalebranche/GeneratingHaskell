module SignedSort where


data Parity = Even | Odd deriving (Eq,Ord,Show)
instance Num Parity where
	fromInteger i = if even i then Even else Odd
	a + b = if a==b then Even else Odd
	Odd*Odd = Odd
	_ * _ = Even
	(-) = (+) 
	negate = id
	abs = id
	signum = id
	
-- sortiert Listen unter Berücksichtigung, daß die Vertauschung zweier
-- ungerader Elemente ein Vorzeichen verursacht
-- compare ist die Vergleichsfunktion
-- par muß das Vorzeichen zurückgeben
signedSort compare par list = let
	(res,k) =  ss (zip list $ map par list) (length list) 
	toSign Odd = negate
	toSign Even = id
	ss l 0 = (l,1 :: Int)
	ss l 1 = (l,1)
	ss l n = let 
		h = div n 2
		(a,ka) = ss (take h l) h
		(s,d) = dropSigned h l
		(b,kb) = ss d (n-h)
		(m,k) = merge s a b
		in (m,k*ka*kb)
	merge s [] b = (b,1)
	merge s a [] = (a,1)
	merge s a@((x,xs):ar) b@((y,ys):br) = case (xs*ys, compare x y) of
		(_, GT) -> let (m,k) = merge s a br in ( (y,ys) : m, toSign (s*ys) k) 
		(Odd,EQ) ->let (m,k) = merge (s-xs) ar b in ((x,xs) : m, 0)
		_  -> let (m,k) = merge (s-xs) ar b in ((x,xs) : m,k)
	dropSigned 0 l = (0,l)
	dropSigned n ((_,a):l) = let (g,d) = dropSigned (n-1) l 
		in (g+a,d)
	in (map fst res , fromIntegral k) 



