map :: (a -> b) -> [a] -> [b]
map f (x:xs) = (f x) : (map f xs) 
map _ [] = []

square :: Int -> Int
square x = x*x

doublelarge :: [Int] -> [Int]
doublelarge xs = [x * 2 | x <- (map square xs), x > 3]

demo = doublelarge [2,4,5]
demo2 = doublelarge [] 
