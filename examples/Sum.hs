module Sum where 

sum' :: Num a => [a] -> a 
sum' (x:xs) = x + sum' xs
sum' [] = 0

demo = sum' [1..5]
