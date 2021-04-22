sum :: Num a => [a] -> a 
sum xs = if (not (null xs)) then (head xs) + sum (tail xs) else 0

demo = sum [1,2,3]