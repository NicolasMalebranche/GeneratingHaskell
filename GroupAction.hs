{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}

-- Gruppenwirkungen
module GroupAction where

import Data.List
import qualified Data.Set as Set

-- Gruppenwirkungen
class GroupAction g x where
	gAct :: g -> x -> x

instance GroupAction g x => GroupAction g [x] where
	gAct g = map (gAct g)

instance GroupAction g x => GroupAction g [(x,a)] where
	gAct g l = [ (gAct g x,a) | (x,a) <- l ]

instance (Ord x,GroupAction g x) => GroupAction g (Set.Set x) where
	gAct g = Set.map (gAct g)


-- Orbit eines Elements x unter der Gruppe erzeugt von gen
gOrbit gen x = run (Set.singleton x) where
	run s = if s==ns then s else run ns where
		ns = Set.unions $ s : [gAct g s | g <- gen]

-- Orbits einer Menge von Elementen
gOrbits gen s = run s where
	run s = if Set.null s then [] else or : run (s Set.\\ or) where
		or = gOrbit gen $ head $ Set.elems s

-- Findet kürzesten Weg aus Elementen von gen, um von x nach y zu gelangen		
gPath gen x y = run (Set.singleton $ Lab x []) where
	yy = Lab y undefined
	run s = let 
		Just (Lab _ path) = Set.lookupLE yy s 
		ns = Set.unions $ s : [gAct g s | g <- gen]
		in
		if Set.member yy s then Just path else 
		if  s==  ns then Nothing else run ns 

data Labeled a i = Lab a i deriving Show
instance (Eq a) => Eq (Labeled a i) where
	Lab a _ == Lab b _  = a==b
instance (Ord a) => Ord (Labeled a i) where
	Lab a _ `compare` Lab b _  = compare a b
instance (GroupAction g a) => GroupAction g (Labeled a [g]) where
	gAct g (Lab a p) = Lab (gAct g a) (g:p)

-- Ist x ein invariantes Element?
gInvariant gen x = all (x ==) [ gAct g x | g <- gen ]


