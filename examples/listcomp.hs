doublelarge :: [Int] -> [Int]
doublelarge xs = [x * 2 | x <- xs, x > 3]

demo = doublelarge [2,4,5]
