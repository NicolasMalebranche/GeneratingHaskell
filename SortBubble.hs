module SortBubble where


-- Sortiert eine Liste mit Bubblesort
-- Die Vergleichsfunktion soll zwei Elemente in die richtige Reihenfolge bringen;
sortBubble compare = s where
	s [] = []
	s (a:r) = case s r of
		[] -> [a]
		b:sr -> case compare a b of	
			[] -> sr
			x:y -> x : s (y++sr)