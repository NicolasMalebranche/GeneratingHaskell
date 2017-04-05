{-# LANGUAGE InstanceSigs #-}
module TrieSet where

import Prelude hiding (null,lookup,filter,map)
import qualified Prelude as P
import Data.MemoTrie
import Cantor

-- Mengen von möglicherweise unendlicher Mächtigkeit
-- contains: ist ein Element in der Menge enthalten?
-- elems: abzählbar viele Elemente der Menge in beliebiger Reihenfolge
data TrieSet a = TrieSet {contains :: a -> Bool, elems :: [a]}

null s = case elems s of
	[] -> True
	_  -> False
size s = length $ elems s
member = flip contains
notMember i = not . member i
isSubsetOf a b = all (contains b) (elems a)

empty = TrieSet {contains = const False, elems = []}
singleton a = TrieSet {contains = (==) a, elems = [a]}
insert a s = TrieSet {contains = memo c, elems=e} where
	c i = (a==i) || contains s i 
	e = a : P.filter (/= a) (elems s)
fromList l = foldr insert empty l
delete a s = TrieSet {contains = memo c, elems=e} where
	c i = (a/=i) && contains s i
	e =  P.filter c (elems s)


union a b = TrieSet {contains = memo c , elems = e} where
	e = cantor [elems a, P.filter (not . contains a) (elems b)]
	c i = contains a i || contains b i

unions lt = TrieSet {contains = memo c, elems = e} where
	c i = foldr ( (||) . member i ) False lt
	un _ [] = []
	un f (s:r) = P.filter f (elems s) :
		un (\i -> f i && not (contains s i)) r
	e = cantor (un (const True) lt)

intersection a b = TrieSet {contains = memo c, elems = e} where
	e = P.filter (contains a) (elems b)
	c i = contains a i && contains b i

difference a b = (\\) a b
(\\) a b = TrieSet (memo x) l where
	x i = contains a i && not (contains b i)
	l = P.filter (not . contains b) (elems a)

filter f s = TrieSet {contains = memo c, elems = e} where	
	c i = contains s i && f i
	e = P.filter f (elems s)

map f s = fromList $ P.map f (elems s)
	
instance (Eq a, HasTrie a) => Eq (TrieSet a) where
	a==b = all (contains b) (elems a) && 
		   all (contains a) (elems b)

instance (Show a) => Show (TrieSet a) where
	show s = '{' : (init.tail.show.elems) s ++ "}"
