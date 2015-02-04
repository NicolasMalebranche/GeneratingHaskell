
module Infinity where


-- Erweitert Zahlen um +- unendlich

data TransFinite a = Finite a | Infinity | NegInfinity deriving (Eq)

instance Ord a => Ord (TransFinite a) where
	compare Infinity Infinity = EQ
	compare (Finite a) (Finite b) = compare a b
	compare NegInfinity NegInfinity = EQ
	compare Infinity _ = GT	
	compare NegInfinity _ = LT
	compare _ Infinity = LT
	compare _ NegInfinity = GT

instance Bounded (TransFinite a) where
	minBound = NegInfinity
	maxBound = Infinity

instance (Show a) => Show (TransFinite a) where
	show (Finite a) = show a
	show Infinity = "Inf"
	show NegInfinity = "-Inf"

-- Die Listen, die erzeugt werden, sind  
-- ausschliesslich mit endlichen Werten gefuellt
instance Enum a => Enum (TransFinite a) where
	toEnum = Finite . toEnum
	fromEnum (Finite a) = fromEnum a
	enumFrom t = enumFromTo t Infinity
	enumFromThen t x = enumFromThenTo t x Infinity
	enumFromTo Infinity _ = []
	enumFromTo (Finite a) Infinity = map Finite $ enumFrom a
	enumFromTo (Finite a) (Finite b) = map Finite $ enumFromTo a b
	enumFromTo _ NegInfinity = []
	enumFromTo NegInfinity Infinity = map Finite $
		listMerge (iterate pred nl) (iterate succ $ succ nl) where 
			nl = toEnum 0
			listMerge [] b = b
			listMerge a [] = a
			listMerge (x:a)(y:b) = x:y:listMerge a b
	enumFromTo NegInfinity (Finite b) = map Finite $ iterate pred b
	--enumFromThenTo Infinity _ _ = []	
	--enumFromThenTo (Finite a) Infinity Infinity = [Finite a]
	enumFromThenTo (Finite a) (Finite b) Infinity = 
		case enumFromTo a b of {[]-> []; _ -> map Finite $ enumFromThen a b}
	enumFromThenTo (Finite a) (Finite b) (Finite c) = map Finite $ enumFromThenTo a b c
	enumFromThenTo (Finite a) (Finite b) NegInfinity = 
		case enumFromTo a b of {[] -> map Finite $ enumFromThen a b ; _ -> [] }
	--enumFromThenTo (Finite a) NegInfinity NegInfinity = [Finite a]
	--enumFromThenTo NegInfinity (Finite a) Infinity = [Finite a]
	--enumFromThenTo NegInfinity (Finite a) (Finite b)  = 
	--	case enumFromTo a b of {[] ->[]; _ -> [Finite a]}
	--enumFromThenTo NegInfinity (Finite b) NegInfinity = [] 
	--enumFromThenTo _ Infinity _ = []
	--enumFromThenTo _ NegInfinity _ = []
	--enumFromThenTo _ _ NegInfinity = []
	succ (Finite a) = Finite $ succ a
	pred (Finite a) = Finite $ pred a


instance (Ord a, Num a) => Num (TransFinite a) where
	Finite a + Finite b = Finite $ a+b
	Infinity + NegInfinity = error "Inf-Inf=?"
	NegInfinity + Infinity = error "Inf-Inf=?"
	Infinity + _ = Infinity
	_ + Infinity = Infinity
	NegInfinity + _ = NegInfinity
	_ + NegInfinity = NegInfinity
	negate (Finite a) = Finite $ negate a
	negate Infinity = NegInfinity
	negate NegInfinity = Infinity
	abs (Finite a) = Finite $ abs a
	abs Infinity = Infinity
	abs NegInfinity = Infinity
	signum (Finite a) = Finite $ signum a
	signum Infinity = 1
	signum NegInfinity = -1
	fromInteger = Finite . fromInteger
	Infinity * Infinity = Infinity
	Infinity * (Finite a) = case compare a 0 of 
		{GT -> Infinity; LT -> NegInfinity; EQ -> error "Inf*0=?" }
	Infinity * NegInfinity = NegInfinity
	Finite a * Finite b = Finite $ a+b
	Finite a * NegInfinity = case compare 0 a of
		{GT -> Infinity; LT -> NegInfinity; EQ -> error "Inf*0=?" }
	NegInfinity * NegInfinity = Infinity
	x*y = y*x

instance (Ord a, Fractional a) => Fractional (TransFinite a) where 
	fromRational = Finite . fromRational
	recip (Finite a) = Finite $ recip a
	recip Infinity = 0
	recip NegInfinity = 0





