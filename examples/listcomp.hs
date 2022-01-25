map :: (a -> b) -> [a] -> [b]
map f (x:xs) = (f x) : (map f xs) 
map _ [] = []

square :: Integer -> Integer
square x = x*x

doublelarge :: [Integer] -> [Integer]
doublelarge xs = [x * 2 | x <- xs, x > 3]

take :: Integer -> [a] -> [a]
take 0 _ = []
take n (x:xs) = x : (take (n-1) xs)
take _ [] = []