map :: (a -> b) -> [a] -> [b]
map f (x:xs) = (f x) : (map f xs)
map _ [] = []

square :: Num a => a -> a 
square x = x*x 

sum :: Num a => [a] -> a
sum (x:xs) = x + sum xs
sum [] = 0

--This is an example of using a higher order function (map)
--This works with `square` supported, or a lambda expression, which is not
demo = map (\x -> x * x) [1..3]
