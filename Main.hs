import HilbK3

main = do 
	putStr "write 24 matrix: n=2"
	write24 2
	putStr ", 3"
	write24 3
	putStrLn ", 4"
	write24 4
	putStr "write Sym3 matrix: n=2"
	writeSym3 2
	putStr ", 3"
	writeSym3 3
	putStrLn ", 4"
	writeSym3 4
	putStr "write Sym2 matrix: n=2"
	writeSym2 2
	putStr ", 3"
	writeSym2 3
	putStrLn ", 4"
	writeSym2 4
{-	putStrLn "write the rest"
	write24 5
	write24 6
	write24 7
	writeSym3 5
	writeSym3 6
	writeSym3 7
-}	putStrLn "Done."
