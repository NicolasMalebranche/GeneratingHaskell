module HilbK3 where

-- Modul für Multiplikationen nach Lehn und Sorger

import Data.Array
import Data.MemoTrie
import K3
import LinearAlgebra
import Permutation
import Partitions
import Data.Permute


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
--fTop pi tau v 

cup g f (part, c) = su