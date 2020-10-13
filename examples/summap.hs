sum :: Num a => [a] -> a 
sum (x:xs) = x + (sum xs) 
sum [] = 0

map :: (a -> b) -> [a] -> [b]
map f (x:xs) = (f x) : (map f xs)
map _ [] = []

add :: Int -> Int -> Int 
add x y = x + y

--Here we can use a partial function, and function composition

sum (map (add 3) [1,2,3])
