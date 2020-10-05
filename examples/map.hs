map :: (a -> b) -> [a] -> [b]
map f (x:xs) = (f x) : (map f xs)
map _ [] = []

square :: Int -> Int 
square x = x*x 

map square [1..3]