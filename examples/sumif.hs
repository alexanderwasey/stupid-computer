sum :: [Int] -> Int 
sum xs = if (length xs > 0) then (head xs) + sum (tail xs) else 0

length :: [Int] -> Int
length (x:xs) = 1 + (length xs) 
length [] = 0 

sum [1,2,3]
