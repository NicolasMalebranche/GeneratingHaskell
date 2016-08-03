import LS_Operators
import LS_Frobenius
import Data.Ratio
import PowerSeries

kah = K3 7
[(_,kah2)] = gfa_mult kah kah
nk op n k = let
	Vak sta = jState $ replicate (2*k) (Ch 0 kah) ++ replicate n (J 0 (-1) 0)
	alpha = (fromIntegral $ product [1..n] * product [1,3..2*k-1])* kah2 ^ k * (-1) ^ n
	in toJ$ Vak [ (o++v,x*y/alpha) | (o,x) <- op, (v,y) <-  sta ]

test k n = nk (cT $ 2*k) n (n-k) 
chern k n = nk [([ChT $ 2*k],fromIntegral $ product [1..2*k])] n (n-k)

-- chern k n = (gamma k + (n-k)*beta k) * Vak q_1(x)^n
beta k = let 
	kk = fromIntegral k 
	fact n = if n ==0 then 1 else n*fact (n-1) 
	in numerator$ (-1)^k*(fact(2*k+2)*fact(2*k))%(fact k ^2* fact (k+1)^2 )
gamma k = let kk = fromIntegral k 
	in 
	numerator $ 2*(-4)^k * (product [1..kk+1]*product[1,3..2*kk-3]*product[1,3..2*kk+1])%(product[1..kk]^3)


-- der große test
zz n k = (gamma k + (n-k)*beta k) 
zahl n k =  kah2 ^(n-k) *2*(-4)^k * (z%nen) where
	z = product [1,3..2*n-2*k-1] * product [1,3..2*k+1] *product [1,3..2*k-3] * ((k+1)^2 +(n-k)*(2*k-1))
	nen = product [1..k]*product[1..k+1]*product[1..2*k]
pro n k = scale (1/product [1..fromIntegral n]) $ toNaka $ jState $ ChT (2*k) : replicate (2*n-2*k) (Ch 0 kah) ++ replicate n (P (-1) 0)

-- Ellingsrud - Göttsche - Lehn
eglH psi phi = seriesGenerating $ map f [0..] where
	f n = case toNaka $ mul n of 
		Vak [] -> 0
		Vak [(_,x) ] -> x*(-1)^n  
	mul n = toJ $ Vak [ (o++o'++a,x*x'*y) | k <- [0..2*n] , (o,x) <- psi k, (o',x') <- phi (2*n-k), (a,y) <- unVak $ one n ]

eglCh = eglH psi phi where
	psi n = [(replicate n (Del :: VertexOperator K3Domain),1)] 
	phi = cT

-- Rekursiv für Chernklassen
cc c = (!!) list where
	list = nakaState [] : map f list 
	f (Vak s) = toNaka$ toJ $Vak [ (t++[Ch 0 kah, Ch 0 kah, P(-1) 0] ++ o , x*y)| (o,x) <- s, (t,y) <- c]


