{-# LANGUAGE TypeOperators, TypeFamilies #-}

module Partitions where

import Data.Permute
import Data.Maybe
import qualified Data.List 
import Data.MemoTrie

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
	
	-- Nächste Partition
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

-----------------------------------------------------------------------------------------

-- Datentyp für Partitionen in Alpha-Schreibeweise
-- (Liste von Muliplizitäten)
newtype PartitionAlpha = PartAlpha { alphList::[Int] }


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
	partAsAlpha = id
	partFromAlpha = id
	partAsLambda (PartAlpha l) = PartLambda $ reverse $ f 1 l where
		f i [] = []
		f i (0:r) = f (i+1) r
		f i (m:r) = i : f i ((m-1):r)
	partFromLambda = lambdaToAlpha
	partAllPerms = partAllPerms . partAsLambda
	partSucc (PartAlpha a) = PartAlpha $ find 0 1 a where
		find v i [] = [v+1]
		find v i (0:r) = find v (i+1) r
		find 0 i (1:r) = find i (i+1) r
		find 0 1 (k:r) = k-2 : augment r
		find 0 i (k:r) = construct 1 [(i-1,1),(i,k-2)] ++ augment r
		find 1 i (k:r) = construct 1 [(i,k-1)] ++ augment r
		find v i (k:r) = construct 1 [(v-1,1),(i,k-1)] ++ augment r
		augment [] = [1]
		augment (a:r) = a+1:r
		construct _ [] = []
		construct i l@((j,v):r)= if i==j then v:construct(i+1)r else 0:construct (i+1) l

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
		mysuc r = fromJust $ my r where
			my [a] = Nothing
			my (a:b:r) = combine $ my $ b:r where
				combine Nothing = if b==1 then Just $ a+1:r else Just $ a+1:b-1:r
				combine (Just (c:r)) = if c>a then Just $ c:a:r else Just $a:c:r

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
