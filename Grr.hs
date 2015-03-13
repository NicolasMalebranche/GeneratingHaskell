
import InfinitePolynomial
import Data.Array
import MatrixAlgorithms
import Data.Numbers.Primes(primes)
import Data.List
import LinearAlgebra
import Data.MemoTrie
import Elementary



--ind bil p q = sum $ map (product. zipWith bil p) $ permutations q
--ahat nn kk = let [n,k] = map toInteger [nn,kk] in
--	product [ factorial (k-i) ^ bin (n-2+i) i | i<-[0..k-1]  ] ^ n 

{-
ind bil p q = sum $ map (product.map(uncurry bil)) $ pairpartitions $ p++q
pairpartitions [] = [[]]
pairpartitions (a:r) = [(a,b):y | (b,x) <- take1 [] r, y<-pairpartitions x] where
	take1 v (x:h)  = (x,v++h) : take1 (v++[x]) h
	take1 _ [] = []
b i j = if i==j then 1 else 0

-}

indmat  vs n = listArray ((1::Int,1::Int),(l,l)) [inb i j | i<-s, j<-s] where s = sym n vs; l = length s


inb a b = product [ if even k then ffacs !! div k 2 else 0 | x<-group $ sort $ a++b , let k = length x] 

ffacs = 1 : zipWith (*) ffacs [1,3..]

bin n k = div (product [n-i | i<-[0..k-1]]) (factorial k)



sym 0 _ = [[]]
sym n [] = []
sym n t@(a:r) = map (a:) (sym (n-1) t) ++ sym n r

asym 0 _ = [[]]
asym n [] = []
asym n (a:r) = map (a:) (asym (n-1) r) ++ asym n r



f2 n l = accumArray ((flip mod 2.).(+)) 0 (1,n) $ zip l $ repeat 1

allf2 n = map (listArray (1,n)) $  al n where
	al 0 = [[]]
	al n = map (0:) aln ++ map (1:) aln where aln = al (n-1)

indSubMat f2a k = listArray ((1,1),(dim,dim)) [inb i j | i <-vs, j<-vs ] where
	(1,n) = bounds f2a
	vs = [ a | a<-sym k [1..n], f2 n a == f2a ]
	dim = length vs

asub f2a k = last $ berkowitz [1..dim] ism where
	ism = listArray ((1,1),(dim,dim)) [inb i j | i <-vs, j<-vs ] where
	(1,n) = bounds f2a
	vs = [ a | a<-sym k [1..n], f2 n a == f2a ]
	dim = length vs

a n k = product [ asub (listArray (1,n) (replicate i 0++replicate (n-i) 1)) k ^bin n ii | ii<-[0..n],let i =fromIntegral ii]

primeFactors n = [(head x, length x) | x<- group $check primes $ abs n] where
	check _ 1 = []
	check l@(p:r) n = if m==0 then p:check l d else check r n where (d,m) = divMod n p 


obj n i = sum [fromInteger (sig p)* x_ (p!!i) | p<-permutations [1..n]] where
sig p =  product [signum $ (a-b)*(i-j) | [(a,i),(b,j)] <- asym 2 $ zip [1..] p]


sodd n k = product [ i^bin (k-i+n-1) (n-1) | i<-[1,3..2*(k-1)+n]] * product [ i^((n-1)*bin (k-i+n-1) (n-1)) | i<- [1..k]]
--seve n k = product [ i^(i*(2+bin (k-i-1) 2)) | i<-[1..k+1]] * product [ i^((n-1)*bin (k-i+n-1) (n-1)) | i<- [1..k]] 

printmap f [] = return 0;
printmap f (a:r) = do
	putStr $ show a ++ ":\t"
	print $ f a
	printmap f r

