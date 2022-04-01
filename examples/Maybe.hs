mayInt :: (Maybe Integer) -> Integer 
mayInt (Just i) = i
mayInt Nothing = 0

--Example using constructor
demo = mayInt (Just 10)