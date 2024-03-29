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

To download and install run the following commands in your terminal.

`git clone https://github.com/alexanderwasey/stupid-computer.git`

`cd stupid-computer`

`stack install`

And then run the sum examples with 

`stupid-computer examples/sum.hs` , followed by `sum [1, 2, 3, 4]`

For help run `stupid-computer --help`

Source can be found at https://github.com/alexanderwasey/stupid-computer
