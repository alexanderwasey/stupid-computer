sum :: Num a => [a] -> a 
sum (x:xs) = x + (sum xs) 
sum [] = 0

map :: (a -> b) -> [a] -> [b]
map f (x:xs) = (f x) : (map f xs)
map _ [] = []

square :: Int -> Int 
square x = x*x 

sum (map square [1..3])