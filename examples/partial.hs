map :: (Int -> Int) -> [Int] -> [Int]
map f (x:xs) = (f x) : (map f xs)
map _ [] = []

--An example of using a partial function
add :: Int -> (Int -> Int) 
add x = (+) x

map (add 42) [1,2,3]
