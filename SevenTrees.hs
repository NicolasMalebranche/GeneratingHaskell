module SevenTrees where

import System.Random

-- Implementation des Isomorphismus in 
-- http://www.math.lsa.umich.edu/~ablass/7trees.pdf

-- Binary Tree
data T = N T T | L deriving (Show,Eq)

-- Interpretiert Liste als KlammerFolge [[[a,b],c],...]
treeFromList (a:r) = foldl N a r

mShow (N a b) = "["++mShow a ++","++mShow b++"]"
mShow L = "L"

-- Isomorphismus Seven in One
sio (t1@(N _ _),t2,t3,t4,t5,t6,t7) = treeFromList [t7,t6,t5,t4,t3,t2,t1]
sio (L,t2@(N _ _),t3,t4,t5,t6,t7) = treeFromList [t7,t6,t5,t4,t3,t2,L]
sio (L,L,t3@(N _ _),t4,t5,t6,t7) = treeFromList [t7,t6,t5,t4,t3,L,L]
sio (L,L,L,t4@(N _ _),t5,t6,t7) = treeFromList [t7,t6,t5,t4,L,L,L]
sio (L,L,L,L,t5@(N a b),t6,t7) = treeFromList [L,t7,t6,a,b]
sio (L,L,L,L,L,t6@(N _ _),t7) = treeFromList [t6,t7,L,L,L,L]
sio (L,L,L,L,L,L,t7@(N(N(N(N a b)c)d)e)) = treeFromList [L,a,b,c,d,e]
sio (L,L,L,L,L,L,t7) = t7

-- Isomorphismus One in Seven
ois (N(N(N(N(N(N(t7)t6)t5)t4)t3)t2)t1@(N _ _)) = (t1,t2,t3,t4,t5,t6,t7)
ois (N(N(N(N(N(N(t7)t6)t5)t4)t3)t2@(N _ _))L) = (L,t2,t3,t4,t5,t6,t7)
ois (N(N(N(N(N(N(t7)t6)t5)t4)t3@(N _ _))L)L) = (L,L,t3,t4,t5,t6,t7)
ois (N(N(N(N(N(N(t7)t6)t5)t4@(N _ _))L)L)L) = (L,L,L,t4,t5,t6,t7)
ois (N(N(N(N(L)t7)t6)a)b) = (L,L,L,L,N a b,t6,t7)
ois (N(N(N(N(N(t6)t7)L)L)L)L) = (L,L,L,L,L,t6,t7)
ois (N(N(N(N(N(L)a)b)c)d)e) = (L,L,L,L,L,L,N(N(N(N a b)c)d)e)
ois t7 = (L,L,L,L,L,L,t7)


-- Zufaelliger binaerer Baum
randomTree = do
	x <- randomIO :: IO Int	
	if odd x then do
		l <- randomTree
		r <- randomTree
		return $ N l r
		else return L

-- Test des Isomorphismus
testISO = do
	t0 <- randomTree
	t1 <- randomTree
	t2 <- randomTree
	t3 <- randomTree
	t4 <- randomTree
	t5 <- randomTree
	t6 <- randomTree
	t7 <- randomTree
	let tup = (t1,t2,t3,t4,t5,t6,t7)
	return (ois (sio tup) == tup, sio (ois t0) == t0)

-- mehrfacher Test
test n = if n<1 then putStrLn "Bestanden." else do
	(a,b) <- testISO
	if a==False || b==False then putStrLn "Test nicht bestanden!" else test (n-1)


