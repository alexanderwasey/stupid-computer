sum :: [Int] -> Int 
sum xs | not (null xs)  = (head xs) + sum (tail xs)
       | otherwise = 0 

sum [1,2,3]
