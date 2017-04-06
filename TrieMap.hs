module TrieMap where

import Prelude hiding (null,lookup)
import qualified TrieSet
import Data.Maybe
import Data.MemoTrie

infixl 9 !?
infixl 9 !

data TrieMap k v = TrieMap { (!?) :: k -> Maybe v, keys :: [k] }

m ! k = fromJust (m !? k)

empty = TrieMap { (!?) = const Nothing, keys = []}
singleton k v = TrieMap { (!?) = c , keys = [k]} where
	c i = if k==i then v else Nothing

null m = case keys m of 
	[] -> True
	_ -> False

size m = length (keys m)

lookup = (!?)	

findWithDefault k d m = case m !? k of
	Just v  -> v
	Nothing -> d

insert k v m = TrieMap {(!?) = memo c, keys = ks} where
	c i = if k==i then Just v else m !? i 
	ks = k : filter (/=k) (keys m)

insertWith f k v m = TrieMap {(!?) = memo c, keys = ks} where
	c i = if k==i then Just x else m !? i
	ks = k : filter (/=k) (keys m)
	x = case m !? k of
		Nothing -> v
		Just w  -> f v w

insertWithKey f k = insertWith (f k) k


delete k m = TrieMap {(!?) = memo c, keys = ks} where
	c i = if k==i then Nothing else m !? i
	ks = filter (k/=) (keys m)

adjust f k m = TrieMap {(!?) = memo c, keys = keys m} where
	c i = if k==i then fmap f (m !? k) else m !? k

adjustWithKey f k = adjust (f k) k

update f k m = TrieMap {(!?) = memo c, keys = ks} where
	c i = if k==i then if b then x else Nothing else m !? i 
	ks = k : filter (/=k) (keys m)
	b = not (isNothing (m!?k))
	x = f (fromJust (m !? k))


assocs m = [(k,fromJust $ m!?k) |k <- keys m]
toList = assocs

elems = map snd . assocs 

-- Unendliche Listen sind erlaubt
fromList l = foldr (uncurry insert) empty l

fromTrieSet f s = TrieMap {(!?) = memo c, keys = TrieSet.elems s} where
	c i = case TrieSet.contains s i of
		True  -> Just (f i)
		False -> Nothing
	
instance HasTrie k => Functor (TrieMap k) where
	fmap f m = TrieMap { (!?) = memo c, keys = keys m} where
		c i = fmap f (m !? i)
