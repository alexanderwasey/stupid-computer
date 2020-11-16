sum :: [Int] -> Int 
sum (x:xs) = x + (sum xs) 
sum [] = 0

sum [1,2,3,4]