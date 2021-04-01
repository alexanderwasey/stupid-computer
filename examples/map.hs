map :: (a -> b) -> [a] -> [b]
map f (x:xs) = (f x) : (map f xs)
map _ [] = []

square :: Num a => a -> a 
square x = x*x 

--This is an example of using a higher order function (map)
--This works with `square` supported, or a lambda expression, which is not
map (\x -> x * x) [1..3]