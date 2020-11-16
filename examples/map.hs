map :: (Int -> Int) -> [Int] -> [Int]
map f (x:xs) = (f x) : (map f xs)
map _ [] = []

square :: Int -> Int 
square x = x*x 

--This is an example of using a higher order function (map)
map square [1..3]