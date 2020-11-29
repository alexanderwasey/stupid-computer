sum :: [Int] -> Int 
sum xs = if (not (null xs)) then (head xs) + sum (tail xs) else 0

sum [1,2,3]