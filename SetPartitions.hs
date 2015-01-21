{-# LANGUAGE TypeOperators, TypeFamilies #-}
module SetPartitions where

import Partitions hiding (TrieType,unTrieType)
import Data.Array
import Data.List
import Data.MemoTrie
import qualified Data.PSQueue as Q
import Debug.Trace

-- Mengenpartitionen als Codewoerter
-- Jedem Index wird die Nummer der enthaltenden Menge zugewiesen (>= 1)
-- Fehlende Nummern werden als leere Mengen interpretiert und stellen
-- entartete Fälle dar
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
	a = accumArray (flip (:)) [] (1,foldr max 0 s) $ zip s set

-- Anzahl der Elemente == partWeight.setPartToLambda
setPartSize = length . setPartCode 

-- Anzahl der Teilmengen == partLength.setPartToLambda, im nichtentarteten Fall
setPartLength = foldr max 0 . setPartCode

-- Bestimmt, ob die erste Partition feiner ist als die zweite
setPartFiner (SetPart s) (SetPart c) = 
	length (nub $ zip c s) == length (nub s)

-- Entfernt leere Mengen aus der Partition
setPartNormalize (SetPart s) = SetPart $ map look s where
	q = Q.fromList $ zipWith (Q.:->) (nub s) [0..] ; sq = Q.size q
	look k = sq - i where Just i = Q.lookup k q

-- Entfernt leere Mengen. Stellt die Anzahl der Elemente richtig ein.
-- Wenn neue Elemente hinzukommen, sind sie isoliert
setPartNormalSize n (SetPart s) = 
	setPartNormalize $ SetPart $ take n $ s ++ [foldr max 0 s+1..]

-- Groebste gemeinsame Verfeinerung 
setPartMin (SetPart s) (SetPart c) = SetPart $ map look $ zip s c where
	q = Q.fromList $ zipWith (Q.:->) (nub $ zip s c) [0..] ; sq = Q.size q
	look k = sq - i where Just i = Q.lookup k q

-- Feinste gemeinsame Vergroeberung
setPartMax p1 p2 = run True (ma s) (ma c) $ zip s c  where
	n = max (setPartSize p1) (setPartSize p2)
	[s,c] = map (setPartCode.setPartNormalSize n) [p1,p2]
	ma l = array (1,m) [(i,i)| i<-[1..m]] where m = foldr max 0 l 
	end arr = setPartNormalize . SetPart . map (u !) where
		u = arr // [(i,u!k) | (i,k)<-assocs arr, i/=k]
	run i a b l = if exit then end b c else run (not i) newb a r where
		sorted = map head $ group $ sort l
		grouped = map (map snd) $ groupBy ((.fst).(==).fst) sorted
		exit = i && all (1==) (map length grouped)
		ass x = zip (tail x) (repeat $ newb ! head x)
		newb = b // (concat $ map ass grouped)
		r = [(newb!y,x) | (x,y) <- sorted ]

-- Bestimmt, ob s eine sich kreuzende Partition ist,
-- d. h. ob s = *a*b*a*b* als regulärer Ausdruck ist
-- Nichtkreuzende Partitionen werden durch Catalanzahlen gezählt
setPartCrossing (SetPart s) = f s (-1) (Q.empty) where
	f [] _ _ = False
	f (i:s) p q = case Q.lookup i q of 
		Nothing -> f s (p-1) $ Q.insert i p q
		Just 0 -> True
		Just v -> f s (v-1) $ update v q
	update v q = if p<v then update v $ Q.insert k 0 q else q where
		Just (k Q.:-> p) = Q.findMin q 

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

