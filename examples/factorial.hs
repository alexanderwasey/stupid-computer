fac :: Integer -> Integer 
fac 0 = 1
fac 1 = 1
fac n = n * fac(n-1)