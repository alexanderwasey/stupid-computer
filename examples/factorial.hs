fac :: Int -> Int 
fac n | n <= 1 = 1
      | otherwise = n * fac(n-1)

fac 5