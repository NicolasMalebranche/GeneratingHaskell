{-# LANGUAGE TypeOperators, TypeFamilies #-}
module SetPartitions where

import Partitions hiding (TrieType,unTrieType)
import Data.Array
import Data.List
import Data.MemoTrie

-- Mengenpartitionen als Codewoerter
-- Jedem Index wird die Nummer der enthaltenden Menge zugewiesen (>= 1)
-- Fehlende Nummern werden als leere Mengen interpretiert und stellen
-- entartete Faelle dar
newtype SetPartition = SetPart {setPartCode::[Int]}


-- Partitionen der Menge [1..n]. Algorithmus von Er.
-- Ausgabe: Jedem Index wird die Nummer einer Menge zugewiesen
setPartitions n = sp 0 n [] where
	sp m n c = if n<=0 then [SetPart c] else
		foldr (++) (sp (m+1) (n-1) ((m+1):c)) [sp m (n-1) (i:c) | i<-[1..m]] 

-- Entsprechende numerische Partition
setPartToLambda (SetPart s) = 
	PartLambda $ sortBy (flip compare) $ map length $ group $ sort s

-- Macht eine Liste von Listen daraus
setPartInstances set (SetPart s) = elems a where
	a = accumArray (flip (:)) [] (1,maximum s) $ zip s set

-- Anzahl der Elemente == partWeight.setPartToLambda
setPartSize = length . setPartCode 

-- Anzahl der Teilmengen == partLength.setPartToLambda, im nichtentarteten Fall
setPartLength = maximum . setPartCode

-- Bestimmt, ob die erste Partition feiner ist als die zweite
setPartFiner (SetPart s) (SetPart c) = 
	length (nub $ zip c s) == length (nub c)

-- Behandelt entartete Partitionen so, als ob sie keine leere Mengen enthielten
instance Eq SetPartition where
	SetPart s == SetPart c = length s==length c && ls==lc && ls==lz where
		ls = length (nub s); lc = length (nub c)
		lz = length (nub $ zip s c)

instance Show SetPartition where
	show sp = "{" ++ concat (intersperse "|" shows) ++"}" where
		shows = map (init.tail.show) $ setPartInstances [1..] sp

instance HasTrie SetPartition where
	newtype SetPartition :->: a =  TrieType { unTrieType :: [Int] :->: a }
	trie f = TrieType $ trie $ f . SetPart
	untrie f =  untrie (unTrieType f) . setPartCode
	enumerate f  = map (\(a,b) -> (SetPart a,b)) $ enumerate (unTrieType f)
