addn :: Integer -> (Integer -> Integer)
addn n = (+) n

--Example of partial function application
demo = addn 4 5