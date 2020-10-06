mayInt :: (Maybe Int) -> Int 
mayInt (Just i) = i
mayInt Nothing = 0

mayInt (Just 10)