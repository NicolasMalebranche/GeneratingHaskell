
import Data.MemoTrie

hc = memo c where
    c :: Integer -> Integer
    c 1 = 1
    c 2 = 1
    c n = hc(hc(n-1)) + hc(n - hc(n-1))
    
-- Gilt: n/2 <= hc n <= n
-- hc (3*2^k + x) - hc (3*2^k - x) = x, für alle 0 <= x <= 2^k
-- Rekursion: hc (6*4^k) = 2 * hc (3*4^k)
-- 4 * hc (3*4^k) - hc (3*4^(k+1)) = k-te Catalanzahl
-- sum_k [ hc (3*4^k) *t^k ] = (2 - t*seriesCatalan) / (1 - 4t*)

hc' = memo c where
    c :: Integer -> Integer
    c 1 = 1
    c 2 = 1
    c n = n - hc'(hc'(n-1)) - hc'(n - hc'(n-1))

-- Rekursion: 4 * hc' (3*4^k) - hc' (3*4^(k+1)) + k-te Catalanzahl = 0
-- sum_k [ hc' (3*4^k) *t^k ] = (1 + t*seriesCatalan) / (1 - 4t*)