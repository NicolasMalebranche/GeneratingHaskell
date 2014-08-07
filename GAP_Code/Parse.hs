import Text.Parse

p = parseList :: TextParser [[Int]]

file = "GAP_n=3_24.txt"

s = readFile file

extr (Right l, _) = l

res = s >>= return . extr . runParser p 
