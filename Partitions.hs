{-# LANGUAGE TypeOperators, TypeFamilies, MultiParamTypeClasses, 
	FunctionalDependencies, FlexibleInstances #-}

module Partitions where

import Data.Permute
import Data.Maybe
import qualified Data.List 
import Data.MemoTrie

-- Partitionszahlen, via Pentagonalzahltheorem
partNumber :: Int -> Integer
partNumber = memo pRec where
	pRec 0 = 1
	pRec n = pp pent 1 0 where
		pp (p:q:pr) k acc = if n < p then acc else pp pr (k+2) $
			acc + partNumber (n-p) + partNumber (n-p-k) - 
			partNumber (n-q) - partNumber (n-q-k-1)
	pent = 1 : zipWith (+) [4,7..] pent

-----------------------------------------------------------------------------------------

class (Eq a, HasTrie a) => Partition a where
	-- Länge einer Partition
	partLength :: Integral i => a -> i 
	
	-- Gewicht einer Partition
	partWeight :: Integral i => a -> i
	
	-- Grad einer Partition = Gewicht-Länge
	partDegree :: Integral i => a -> i
	partDegree p = partWeight p - partLength p
	
	-- Das in den Papern übliche z
	partZ :: Integral i => a -> i
	partZ = partZ.partAsAlpha
	
	-- Konjugierte Partition
	partConj :: a -> a
	partConj = res. partAsAlpha where
		make l (m:r) = l : make (l-m) r
		make _ [] = []
		res (PartAlpha r) = partFromLambda $ PartLambda $ make (sum r) r
	-- Um die linke Spalte reduzierte Partition
	partReduceLeft :: a -> a
	-- Um die obere Zeile reduzierte Partition	
	partReduceTop :: a -> a

	-- Inhalte einer Partition = [j-i] fuer alle (i,j) im Ferrers Diagramm
	partContents :: Integral i => a -> [i]
	
	-- Hakenlänge 
	partHookLength :: (Int,Int) -> a -> Int

	-- (vorspringende) Ecken
	partCorners :: a -> [(Int,Int)]

	-- Dominanzordnung
	-- Dominiert das erste Argument das zweite?
	partDominates :: a -> a -> Bool
	partJoin :: a -> a -> a
	partMeet :: a -> a -> a

	-- Nächste Partitiond
	partSucc :: a -> a
	
	-- Leere Partition
	partEmpty :: a
	
	-- Transformation nach Alpha-Schreibweise
	partAsAlpha :: a -> PartitionAlpha
	-- Transformation von Alpha-Schreibweise
	partFromAlpha :: PartitionAlpha -> a
	-- Transformation nach Lambda-Schreibweise
	partAsLambda :: a -> PartitionLambda Int
	-- Transformation von Lambda-Schreibweise
	partFromLambda :: (Integral i, HasTrie i) => PartitionLambda i -> a
	
	-- Alle Permutationen vom entsprechenden Zykeltyp
	partAllPerms :: a -> [Permute]
	
	-- Summe zweier Partitionen
	partAdd :: a -> a -> a

	-- Young's Partialordnung
	partContains :: a -> a -> Bool	
	-- Vereinigung zweier Partitionen
	partUnion :: a -> a -> a
	-- Schnitt zweier Partitionen
	partIntersection :: a -> a -> a

	-- partRank
	partCrank :: a -> Int

-----------------------------------------------------------------------------------------

-- Datentyp für Partitionen in Alpha-Schreibeweise
-- (Liste von Muliplizitäten)
newtype PartitionAlpha = PartAlpha { alphList::[Int] }


-- Smarter Constructor, schneidet die Nullen am Ende ab
partAlpha = PartAlpha . pA [] where
	pA n [] = []
	pA n (0:r) = pA (0:n) r
	pA n (x:r) = n ++ (x : pA [] r)

zipAlpha op (PartAlpha a) (PartAlpha b) = PartAlpha $ zipWith' op a b

-- Normales zipWith aber ohne Abschneiden bei unterschiedlicher Länge
zipWith' op = z where
	z (x:a) (y:b) = op x y : z a b
	z [] (y:b) = op 0 y : z [] b
	z (x:a) [] = op x 0 : z a []
	z [] [] = []

-- Baut eine Partition aus einer liste
partition :: [Int] -> PartitionAlpha
partition = let 
	buildPartition 0 (PartAlpha []) = partEmpty
	buildPartition i (PartAlpha r) = if i<0 then error "negative partition multiplicity" else PartAlpha (i:r)
	in foldr buildPartition partEmpty

-- Setzt ein Element vor eine Partition
alphaPrepend 0 (PartAlpha []) = partEmpty
alphaPrepend i (PartAlpha  r) = PartAlpha (i:r)

instance Partition PartitionAlpha where
	partWeight (PartAlpha r) = fromIntegral $ sum $ zipWith (*) r [1..]
	partLength (PartAlpha r) = fromIntegral $ sum r
	partEmpty = PartAlpha []
	partZ (PartAlpha l) = foldr (*) 1 $ zipWith (\a i -> factorial a * i^a) (map fromIntegral l) [1..] where
		factorial n = if n==0 then 1 else n*factorial(n-1)
	partConj = partAsAlpha . alphaConj	
	partAsAlpha = id
	partFromAlpha = id
	partAsLambda (PartAlpha l) = PartLambda $ reverse $ f 1 l where
		f i [] = []
		f i (0:r) = f (i+1) r
		f i (m:r) = i : f i ((m-1):r)
	partFromLambda = lambdaToAlpha
	partAllPerms = partAllPerms . partAsLambda
	partSucc (PartAlpha a) = PartAlpha $ mys 0 1 a where
		mys s i [] = if s<i then [s+1] else (s-i):[0|_<-[3..i]]++[1]
		mys s i (a:l) = if s<i then  mys (s+i*a) (i+1) l else (s-i):[0|_<-[3..i]]++(a+1):l
	partReduceLeft (PartAlpha (a:r)) = PartAlpha r
	partReduceTop (PartAlpha a) = PartAlpha $ red a where 
		red [] = []; red [1] = [] ; red [b] = [b-1]; red (b:r) = b:red r
	partContents = partContents . partAsLambda
	partHookLength (i,j) (PartAlpha a) = if i<1||j<1 then error "Index to small" else 
		partHookLength (i,1) $ partAsLambda $ PartAlpha $ drop (j-1) a
	partCorners p@(PartAlpha a) = pc (partLength p) 1 [] a where 
		pc _ _ acc [] = acc
		pc i j acc (a:r) = if a>0 then pc (i-fromIntegral a) (j+1) ((i,j):acc) r else pc i (j+1) acc r
	partDominates a b = partDominates (partAsLambda a) (partAsLambda b)
	partJoin a b = partAsAlpha $ partMeet (partAsLambda a) (partAsLambda b)
	partMeet a b = partAsAlpha $ partJoin (partAsLambda a) (partAsLambda b)
	partAdd = zipAlpha (+)
	partContains (PartAlpha a) (PartAlpha b) = pc a b where
		pc _ [] = True
		pc [] b = all (0==) b
		pc (x:r)(y:p) = if x>=y then pc r p else pc r (y-x+a:q) where (a:q) =p++[0]
	partUnion a b = partFromLambda $ partUnion (partAsLambda a) $ partAsLambda b
	partIntersection a b = partFromLambda $ partIntersection (partAsLambda a) $ partAsLambda b
	partCrank (PartAlpha a) = if w== 0 then l else m-w where
		w = if a ==[] then 0 else head a
		l = last$ 0: [ n| (n,m)<- zip [1..] a, m > 0]
		m = sum $ drop w a

-- Alle Partitionen eines bestimmten Gewichts, aufsteigend sortiert
partOfWeight :: Int -> [PartitionAlpha]
partOfWeight = let
	build n 1 acc = [alphaPrepend n acc]
	build n c acc = concat [ build (n-i*c) (c-1) (alphaPrepend i acc) | i<-[0..div n c]] 
	a 0 = [PartAlpha []]
	a w =  if w<0 then [] else  build w w partEmpty
	in memo a

-- Alle Partitionen eines bestimmten Gewicht und einer bestimmten Länge, aufsteigend sortiert
partOfWeightLength = let
	build 0 0 _ = [partEmpty]
	build w 0 _ = []
	build w l c = if l > w || c>w then [] else
		concat [ map (alphaPrepend i) $ build (w-i*c) (l-i) (c+1) | i <- [0..min l $ div w c]]
	a w l = if w<0 || l<0 then [] else build w l 1
	in memo2 a

-- Alle Partitionen eines bestimmten Grades, welche keine Einser enthalten
partOfDegree = let
	build 0 1 acc  = [alphaPrepend 0 acc]
	build 0 c acc = build 0 (c-1) (alphaPrepend 0 acc)
	build d 2 acc = build 0 1 (alphaPrepend d acc)
	build d c acc = concat [build (d-i*c1) c1 (alphaPrepend i acc) | i<-[0..div d c1]] where c1 = c-1
	a d = if d<0 then [] else build d (d+1) partEmpty
	in memo a

-- Bestimmt den Zykeltyp einer Permutation
cycleType :: Permute -> PartitionAlpha
cycleType p = let 
	lengths = Data.List.sort $ map Data.List.length $ cycles p
	count i 0 [] = partEmpty
	count i m [] = PartAlpha [m]
	count i m (x:r) = if x==i then count i (m+1) r else alphaPrepend m (count (i+1) 0 (x:r)) 
	in count 1 0 lengths

-- Baut eine Permutation aus einer Partition, gefüllt mit aufsteigend sortierten Zykeln 
partPermute :: Partition a => a -> Permute
partPermute = let
	make l n acc (PartAlpha x) = f x where
		f [] = cyclesPermute n acc 
		f (0:r) = make (l+1) n acc $ PartAlpha r
		f (i:r) = make l (n+l) ([n..n+l-1]:acc) $ PartAlpha ((i-1):r)
	in make 1 0 [] . partAsAlpha

instance Eq PartitionAlpha where
	PartAlpha p == PartAlpha q = findEq p q where
		findEq [] [] = True
		findEq (a:p) (b:q) = (a==b) && findEq p q
		findEq [] q = isZero q
		findEq p [] = isZero p 
		isZero = all (==0) 

instance Ord PartitionAlpha where
	compare a1 a2 = compare (partAsLambda a1) (partAsLambda a2)

instance Show PartitionAlpha where 
	show p = let
		leftBracket = "(|"  
		rightBracket = "|)" 
		rest [] = rightBracket
		rest [i] = show i ++ rightBracket
		rest (i:q) = show i ++ "," ++ rest q
		in leftBracket ++ rest (alphList p) 

instance HasTrie PartitionAlpha where
	newtype PartitionAlpha :->: a =  TrieType { unTrieType :: [Int] :->: a }
	trie f = TrieType $ trie $ f . PartAlpha
	untrie f =  untrie (unTrieType f) . alphList
	enumerate f  = map (\(a,b) -> (PartAlpha a,b)) $ enumerate (unTrieType f)

-----------------------------------------------------------------------------------------

-- Partitionen in lambda-Schreibweise
newtype PartitionLambda i = PartLambda { lamList :: [i] }

-- Smarter Konstruktor, schneidet Nullen ab
partLambda l = PartLambda $ takeWhile (0<) l

lambdaToAlpha :: Integral i => PartitionLambda i -> PartitionAlpha
lambdaToAlpha (PartLambda []) = PartAlpha[] 
lambdaToAlpha (PartLambda (s:p)) = lta 1 s p [] where
	lta _ 0 _ a = PartAlpha a
	lta m c [] a = lta 0 (c-1) [] (m:a)
	lta m c (s:p) a = if c==s then lta (m+1) c p a else 
		lta 0 (c-1) (s:p) (m:a)

instance (Integral i, HasTrie i) => Partition (PartitionLambda i) where
	partWeight (PartLambda r) = fromIntegral $ sum r
	partLength (PartLambda r) = fromIntegral $ length r
	partEmpty = PartLambda []
	partAsAlpha = lambdaToAlpha
	partAsLambda (PartLambda r) = PartLambda $ map fromIntegral r
	partFromAlpha (PartAlpha l) = PartLambda $ reverse $ f 1 l where
		f i [] = []
		f i (0:r) = f (i+1) r
		f i (m:r) = i : f i ((m-1):r)
	partFromLambda (PartLambda r) = PartLambda $ map fromIntegral r
	partAllPerms (PartLambda l) = it $ Just $ permute $ partWeight $ PartLambda l where
		it (Just p) = if Data.List.sort (map length $ cycles p) == r then p : it (next p) else it (next p)
		it Nothing = []
		r = map fromIntegral $ reverse l
	partSucc (PartLambda l) = PartLambda $ mysuc l where
		mysuc [] = [1]
		mysuc [a] = replicate (fromIntegral (a+1)) 1
		mysuc r@(a:_) = fromJust $ my (a+1) r where
			my x [a] = Nothing
			my x (a:r) = case my a r of	
				Just e  -> Just $ a:e
				Nothing -> if x>a then Just $ (a+1):[1|_<-[2..sum r]] else Nothing
	partReduceLeft (PartLambda l) = PartLambda $ r l where
		r [] = [] ; r (1:_) = []
		r (a:l) = (a-1):r l
	partReduceTop (PartLambda l) = PartLambda $ drop 1 l
	partContents (PartLambda l) = pc 0 l where
		pc _ [] = []
		pc n (a:r) = [n..fromIntegral a+n-1] ++ pc (n-1) r
	partHookLength (i,j) (PartLambda l) = let r = drop (i-1) l ; f = fromIntegral (head (r++[0])) - j 
		in if i<1||j<1 then error "Index to small" else 
			if f<0 then 0 else f + length (takeWhile (fromIntegral j<=) r)
	partCorners (PartLambda l) = p 1 l where
		p _ [] = [] ; p i [j] = [(i,fromIntegral j)]
		p i (j:kr@(k:_)) = if j==k then p (i+1) kr else (i,fromIntegral j) : p (i+1) kr
	partDominates (PartLambda l) (PartLambda m) = check 0 l m where
		check s (a:l)(b:m) = ss >= 0 && check ss l m where ss = s+a-b
		check s [] m = s >= sum m 		
		check _ _ [] = True
	partMeet (PartLambda l) (PartLambda l') = partLambda $ zipWith (-) (tail s) s where
		a = scanl (+) 0 $ l ++ repeat 0
		b = scanl (+) 0 $ l' ++ repeat 0
		s = zipWith min a b
	partJoin a b = partConj $ partMeet (partConj a) (partConj b) 
	partAdd (PartLambda l) (PartLambda m) = PartLambda $ a l m where
		a xl@(x:l) ym@(y:m) | x==y = x : y : a l m
			| x < y = y : a xl m
			| otherwise = x : a l ym
		a [] m = m
		a l [] = l
	partContains (PartLambda l) (PartLambda m) = all id $ zipWith' (>=) l m
	partUnion (PartLambda l) (PartLambda m) = PartLambda $ zipWith' max l m
	partIntersection (PartLambda l) (PartLambda m) = PartLambda $ zipWith min l m
	partCrank (PartLambda lam) = if w== 0 then l else m-w where
		l = if lam == [] then 0 else fromIntegral $ head lam
		w = length $ filter (1==) lam
		m = length $ filter (fromIntegral w < ) lam

instance (Eq i, Num i) => Eq (PartitionLambda i) where
	PartLambda p == PartLambda q = findEq p q where
		findEq [] [] = True
		findEq (a:p) (b:q) = (a==b) && findEq p q
		findEq [] q = isZero q
		findEq p [] = isZero p 
		isZero = all (==0) 

instance (Ord i, Num i) => Ord (PartitionLambda i) where
	compare p1 p2 = if weighteq == EQ then compare l1 l2 else weighteq where
		(PartLambda l1, PartLambda l2) = (p1, p2)
		weighteq = compare (sum l1) (sum l2)

instance (Show i) => Show (PartitionLambda i) where
	show (PartLambda p) = "[" ++ s ++ "]" where
		s = concat $ Data.List.intersperse "-" $ map show p

instance HasTrie i => HasTrie (PartitionLambda i) where
	newtype (PartitionLambda i) :->: a =  TrieTypeL { unTrieTypeL :: [i] :->: a }
	trie f = TrieTypeL $ trie $ f . PartLambda
	untrie f =  untrie (unTrieTypeL f) . lamList
	enumerate f  = map (\(a,b) -> (PartLambda a,b)) $ enumerate (unTrieTypeL f)

-----------------------------------------------------------------------------------------

-- Konjugation von Partitionen ist dann besonders leicht, wenn die Darstellungen gewechselt werden

lambdaConj (PartLambda l) = PartAlpha $ zipWith (-) ll (tail ll ++ [0]) where
	ll = map fromIntegral l

alphaConj (PartAlpha a) = PartLambda $ init $ scanr (+) 0 a

forkDual :: (OtherRepresentation a b, OtherRepresentation b a) =>
	(a -> a -> a) -> b -> b -> b
forkDual op a b = otherConj $ op (otherConj a) (otherConj b)

class (Partition a, Partition b) => OtherRepresentation a b | a->b  where
	otherConj :: a -> b

instance OtherRepresentation PartitionAlpha (PartitionLambda Int) where
	otherConj a = alphaConj a

instance OtherRepresentation (PartitionLambda Int) PartitionAlpha where
	otherConj l = lambdaConj l

