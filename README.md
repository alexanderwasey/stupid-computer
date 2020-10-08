# stupid-computer
## Break down Haskell programs and execute them step by step! 

For instance given the definition of the sum function:  
``` 
sum :: Num a -> [a] -> a 
sum (x:xs) = x + (sum xs)
sum [] = 0
``` 
And an expression to evaluate: 
```
sum [1,2,3,4]
``` 
A trace of the execution can be shown by the Stupid Computer as follows:
``` 
sum [1, 2, 3, 4]
1 + (sum [2,3,4])
1 + (2 + (sum [3,4]))
1 + (2 + (3 + (sum [4])))
1 + (2 + (3 + (4 + (sum []))))
1 + (2 + (3 + (4 + (0))))
1 + (2 + (3 + (4)))
1 + (2 + (7))
1 + (9)
10
```

Examples of input files can be seen in `examples/ ` 

i.e run `stupid-computer examples/sum.hs` from the project root directory for the sum example. 


**To install** run 
`cabal install` 
from within the root directory of the project. 
