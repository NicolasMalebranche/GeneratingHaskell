module HilbK3 where

-- Modul für Multiplikationen nach Lehn und Sorger

import Data.Array
import Data.MemoTrie
import K3
import LinearAlgebra
import Permutation
import Partitions
import Data.Permute
import qualified Data.Set as Set

-- Lehn Sorger Defekt
defect pi tau = div (size pi + 2 - length (cycles pi) - length (cycles tau) 
	- length (cycles (compose pi tau))) 2

-- Erweitert Definitionsbereich auf Permutationen
-- v hat als Index (Partition, [Klassen])
	-- enlarge v hat als Index (Permute, [Klassen])
	--enlarge v (l,a) = v (cycleType pi, a)
-- enlarge v hat als Index ([Zykel], [Klassen])
--enlarge v (l,a) = v (sortBy (flip compare) (map length l), a)

-- In Lehn und Sorger f^(pi,<pi,tau>)
-- eigentlich nicht wohldefiniert, wegen Relevanz der Anordnung
-- das ist aber egal, falls mit symmetrisierten Vektoren gerechnet wird

tripelprodukt zw def (f1,f2) = product [ {-graphdefect-}cupL a ([ ai| (bi,ai) <- f1, Set.isSubsetOf bi b] ++[ai| (bi,ai) <- f2, Set.isSubsetOf bi b])| (b,a) <- zw]