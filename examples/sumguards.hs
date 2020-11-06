sum :: [Int] -> Int 
sum xs |length xs > 0 = (head xs) + sum (tail xs)
       | otherwise = 0 

sum [1,2,3]
