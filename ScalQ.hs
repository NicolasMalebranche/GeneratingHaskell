{-# LANGUAGE FlexibleInstances, UndecidableInstances #-}

module ScalQ where

-- Klasse für Zahlbereiche, welche mit rationalen Zahlen skalierbar sind
class ScalQ a where
	scalQ :: Rational -> a -> a


instance (Fractional a) => ScalQ a where
	scalQ a x = fromRational a * x


