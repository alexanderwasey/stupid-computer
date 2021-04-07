sum :: Num a => [a] -> a 
sum (x:xs) = x + sum xs
sum [] = 0

sum [1,2,3,4]
