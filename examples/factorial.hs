fac :: Integer -> Integer 
fac 0 = 1
fac 1 = 1
fac n = n * fac(n-1)

fac' :: Integer -> Integer
fac' n = if (n <= 1) then 1 else n * fac' (n-1)

fac'' n | n <= 1 = 1
	  | otherwise = n * fac'' (n-1)