sum :: [Int] -> Int 
sum xs = if (not (null xs)) then (head xs) + sum (tail xs) else 0

length :: [Int] -> Int
length (x:xs) = 1 + (length xs) 
length [] = 0 

sum [1,2,3]
