module Sum where 

import Prelude hiding (sum)

sum :: Num a => [a] -> a 
sum (x:xs) = x + sum xs
sum [] = 0

