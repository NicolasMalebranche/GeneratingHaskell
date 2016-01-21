{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}

-- Gruppenwirkungen und endliche Gruppen
module GroupAction where

import Data.Group
import Data.Monoid
import Data.List
import qualified Data.Set as Set


-- (Links-)Gruppenwirkungen
class GroupAction g x where
	gAct :: g -> x -> x

instance GroupAction g x => GroupAction g [x] where
	gAct g = map (gAct g)

instance GroupAction g x => GroupAction g [(x,a)] where
	gAct g l = [ (gAct g x,a) | (x,a) <- l ]

instance (Ord x,GroupAction g x) => GroupAction g (Set.Set x) where
	gAct g = Set.map (gAct g)

instance (GroupAction g x, GroupAction h y) => GroupAction (g,h) (x,y) where
	gAct (g,h) (x,y) = (gAct g x, gAct h y) 

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

-- Erzeugnis der Menge gen
gSpan gen = run (Set.singleton mempty) where
	run s = if s==ns then s else run $ Set.union s ns where
		ns = Set.unions [ Set.map (mappend g) s | g<-gen ] 


-- Stabilisator des Elements x der Gruppe erzeugt von gen.
-- Terminiert, wenn die Gruppe endlich ist
gStabilizer gen x = Set.filter ((x==).flip gAct x) $ gSpan gen

