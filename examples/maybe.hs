mayInt :: (Maybe Int) -> Int 
mayInt (Just i) = i
mayInt Nothing = 0

--Example using constructor
mayInt (Just 10)