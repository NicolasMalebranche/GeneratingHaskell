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

instance (GroupAction g x, GroupAction g y) => GroupAction g (x,y) where
	gAct g (x,y) = (gAct g x, gAct g y) 

instance (GroupAction g x, GroupAction g y, GroupAction g z) 
	=> GroupAction g (x,y,z) where
	gAct g (x,y,z) = (gAct g x, gAct g y, gAct g z) 

instance (GroupAction g x, GroupAction g y, GroupAction g z, GroupAction g u) 
	=> GroupAction g (x,y,z,u) where
	gAct g (x,y,z,u) = (gAct g x, gAct g y, gAct g z, gAct g u) 

-- Orbit eines Elements x unter der Gruppe erzeugt von gen
gOrbit gen x = run (Set.singleton x) where
	run s = if s==ns then s else run ns where
		ns = Set.unions $ s : [gAct g s | g <- gen]

-- Orbits einer Menge von Elementen
gOrbits gen s = run s where
	run s = if Set.null s then [] else or : run (s Set.\\ or) where
		or = gOrbit gen $ head $ Set.elems s
		

-- Ist x ein invariantes Element?
gInvariant gen x = all (x ==) [ gAct g x | g <- gen ]


