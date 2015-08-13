{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module LS_Tor3
	where

import LS_Frobenius
import LS_Hilb
import Data.Ratio

one = scale (1%6) $ nakaState $ replicate 3 $ P (-1) (Tor 0)

d = [(Del,-1%1)]
j a = [(Ch 0 a,1%1)]

-- ist theta ^* d etwa durch 3 teilbar? -- nöö, q(delta ) = 6
-- theta^* d^4
th_del_4 = multLists [d,d,d,d] one `add`
	scale (-24) (multLists [j 1, j 2, j 3, j 4, j 15] one ) `add`
	scale (24) 	(multLists [j 1, j 2, j 13, j 14] one)`add`
	scale (-24)	(multLists [j 1, j 3, j 12, j 14] one)`add`
	scale (24)	(multLists [j 1, j 4, j 11, j 14] one)`add`
	scale (24)	(multLists [j 2, j 3, j 12, j 13] one)`add`
	scale (-24)	(multLists [j 2, j 4, j 11, j 13] one)`add`
	scale (24)	(multLists [j 3, j 4, j 11, j 12] one)`add`
	scale (120)	(multLists [j 1, j 14, j 15] one)`add`
	scale (-120)(multLists [j 2, j 13, j 15] one)`add`
	scale (120)	(multLists [j 3, j 12, j 15] one)`add`
	scale (-120)(multLists [j 4, j 11, j 15] one)

th_del_2 = multLists [d,d] one 	`add`
	multLists [j 1, j 14] one `add`
	multLists [j 13,j 2] one `add`
	multLists [j 3, j 12] one `add`
	multLists [j 11, j 4] one `add`
	scale (-1) (multLists [j 5,j 10] one) `add`
	(multLists [j 6,j 9] one) `add`
	scale (-1) (multLists [j 7,j 8] one) 
	