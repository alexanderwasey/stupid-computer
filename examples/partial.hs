sum :: Num a => [a] -> a 
sum (x:xs) = x + (sum xs) 
sum [] = 0

map :: (a -> b) -> [a] -> [b]
map f (x:xs) = (f x) : (map f xs)
map _ [] = []

--An example of using a partial function
add :: Int -> (Int -> Int) 
add x = (+) x

map (add 42) [1,2,3]
