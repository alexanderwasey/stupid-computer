module Map where 

import Prelude hiding (sum,map,product)


map :: (a -> b) -> [a] -> [b]
map f (x:xs) = (f x) : (map f xs)
map _ [] = []

square :: Num a => a -> a 
square x = x*x 

sum :: Num a => [a] -> a
sum (x:xs) = x + sum xs
sum [] = 0

product :: Num a => [a] -> a 
product (x:xs) = x * product xs
product [] = 1