{-# LANGUAGE OverloadedStrings #-}

import Data.Attoparsec.Char8
import Data.Word
import qualified Data.IntMap as IM
import Control.Applicative
import qualified Data.ByteString as B
import Data.List

import Signature

myParser :: Parser (Int,(Int,Double))
myParser = do
	char '<'
	a <- decimal
	char ','
	b <- decimal
	char ','
	c <- signed decimal
	char '>'
	char ','
	return $ (a,(b,fromIntegral c))

fullParser = many $ myParser <* endOfLine

toMatrix list = let
	grps = groupBy ((.fst).(==).fst) list
	tr = map (\x-> (fst $ head x, map snd x)) grps
	im = IM.fromList tr
	fun i = im IM.! i
	in fun

niceFile = do 
	f <- B.readFile $ "Mag3.txt"
	let Right l =  parseOnly fullParser f
	print $ signature [1..2554] $ toMatrix l

main = print $ parseOnly myParser "<7,8,454>,"
