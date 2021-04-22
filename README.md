# stupid-computer
## Break down Haskell programs and execute them step by step! 

A Haskell tracer, designed with readability in mind.

For instance given the definition of the sum function:  
``` 
sum :: [Int] -> Int 
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
   =  1 + sum [2,3,4]
   =  1 + 2 + sum [3,4]
   =  1 + 2 + 3 + sum [4]
   =  1 + 2 + 3 + 4 + sum []
   =  1 + 2 + 3 + 4 + 0
   =  1 + 2 + 3 + 4
   =  1 + 2 + 7
   =  1 + 9
   =  10
```

Install with `stack install` from the root directory.

Examples of input files can be seen in `examples/ `

i.e run `stupid-computer examples/sumpattern.hs` , followed by `sum [1, 2, 3, 4]` for the sum example.

For help run `stupid-computer --help`
