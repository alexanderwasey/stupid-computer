map :: (a -> b) -> [a] -> [b]
map f (x:xs) = (f x) : (map f xs)
map _ [] = []

--An example of using a partial function
add :: Num a => a -> (a -> a) 
add x = (+) x

map (add 42) [1,2,3]
