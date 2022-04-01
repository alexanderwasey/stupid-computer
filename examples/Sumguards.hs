module Sumguards where 

import Prelude hiding (sum)

sum :: Num a => [a] -> a 
sum xs | not (null xs)  = head xs + sum (tail xs)
       | otherwise = 0 

demo = sum [1,2,3]