# HW2
Author: Martin Meng

This is the repository for HW2 of UNC's COMP 590: Program Verification and Synthesis.

The file [script.py](script.py) contains the code for all questions. The user can run the script in the main directory.  
    ``` Usage: ./script.py ```

The directory [resultingFiles](resultingFiles) contains the output of the script. 
Specifically, the input files of z3 are named "input_x_x" and the output files of z3 are named "output_x_x".

## Problem 1 [Silly Puzzles] 

### 1.1
#### Question: 
There is a basket containing an apple, a banana, a cherry and a date. Four children named Erica, Frank, Greg and Hank are each to be given a piece of the fruit.
```
(a) Erica likes cherries and dates. 
(b) Frank likes apples and cherries.
(c) Greg likes bananas and cherries.
(d) Hank likes apples, bananas, and dates.
```

#### Solution: 
We have 4 kids and 4 fruits. Every kid likes 2 to 3 kinds of fruits.

    Step 1: make constants for kids and fruits.
    Step 2: add constraints that formulate.
        2.1: if a kid chooses one fruit, then she cannot choose another.
        2.2: if a fruit is chosen by a kid, then it cannot be choosen by other kids.
    Step 3: add kids' preference.
    Step 4: check sat and get model.

The implementation of this plan is in the method problem_1_1() in [script.py](script.py).

The result file is shown in [resultingFiles/output_1_1](resultingFiles/output_1_1). It says that one possible assignment is: 

```
Erica gets date
Frank gets apple
Greg gets cherry
Hank gets banana
```

### 1.2
#### Question: 
Three fellows accused of stealing CDs make the following statements:
```
• Ed: “Fred did it, and Ted is innocent”.
• Fred: “If Ed is guilty , then so is Ted”.
• Ted: “’Im innocent , but at least one of the others is guilty”.
```
If the innocent told the truth and the guilty lied, who is guilty?

#### Solution: 
Let us assume that at least one person is innocent and at least one guilty. So there is one or two guilty guys. We can encode whether a person is guilty or not with a boolean variable. If the boolean value is true, then the person is guilty. 

    Step 1: make boolean variables for each person.
    Step 2: add the constraint for each person.

The smt command is here:

    (declare-const is_Ed_guilty Bool)
    (declare-const is_Fred_guilty Bool)
    (declare-const is_Ted_guilty Bool)
    
    (assert (=> (not is_Ed_guilty) (and is_Fred_guilty (not is_Ted_guilty))))
    (assert (=> (not is_Fred_guilty) (and is_Ed_guilty is_Ted_guilty)))
    (assert (=> (not is_Ted_guilty) (or is_Ed_guilty is_Fred_guilty)))

    (check-sat)
    (get-model)
    
The implementation of this plan is in the method problem_1_2() in [script.py](script.py).

The result is here, also shown in the file [resultingFiles/output_1_2](resultingFiles/output_1_2):
```
sat
(model 
  (define-fun is_Fred_guilty () Bool
    true)
  (define-fun is_Ted_guilty () Bool
    false)
  (define-fun is_Ed_guilty () Bool
    false)
)
```

So one possible case is that Fred is guilty but Ted and Ed are innocent. But if we assume Fred is innocent and add this assertion to our query, we can find out another possibility: Fred is innocent but Ted and Ed are guilty.

The smt command is here:

    (declare-const is_Ed_guilty Bool)
    (declare-const is_Fred_guilty Bool)
    (declare-const is_Ted_guilty Bool)
    
    (assert (=> (not is_Ed_guilty) (and is_Fred_guilty (not is_Ted_guilty))))
    (assert (=> (not is_Fred_guilty) (and is_Ed_guilty is_Ted_guilty)))
    (assert (=> (not is_Ted_guilty) (or is_Ed_guilty is_Fred_guilty)))

    (assert (not is_Fred_guilty))

    (check-sat)
    (get-model)

and the result is here:

```
sat
(model 
  (define-fun is_Ted_guilty () Bool
    true)
  (define-fun is_Fred_guilty () Bool
    false)
  (define-fun is_Ed_guilty () Bool
    true)
)
```

## Problem 2 [Graph Coloring] 
#### Question: 
Attached with this homework are four files with description of graphs. The first line in the file gives the list of vertices (from 0 to n − 1). The second line contains a sequence of pairs that represents the edges in the graphs. Use SAT solver to encode the coloring constraints and find out the colorability of the graphs.

#### Solution: 
This problem asks how many colors are needed to color each graph. We can change this quantity problem to be a decision problem by quering "is the constraint satisfiable under 1 color, 2 colors, ..."

Let's consider one such decision problem. Suppose we have n nodes and m colors. Then for each node we need to create m boolean variable: 
```
1_1, 1_2, ..., 1_m, 
2_1, 2_2, ..., 2_m, 
..., 
n_1, n_2, ..., n_m.  
```
The variable i_j == true iff node i has color j.  

We also need to consider the following constraints.  

Constraint 1: each node needs to have a color.
```
1_1 or 1_2 or ... or 1_m, 
..., 
n_1 or n_2 or ... or n_m.  
```

Constraint 2: each node has a unique color.
```
(1_1 => not (1_2 or 1_3 or ... or 1_m)) and (1_2 => not (1_1 or 1_3 or ... or 1_m)) and ... and (1_m => not (1_1 or 1_2 or ... or 1_m-1))
...
(n_1 => not (n_2 or n_3 or ... or n_m)) and (n_2 => not (n_1 or n_3 or ... or n_m)) and ... and (n_m => not (n_1 or n_2 or ... or n_m-1))
```              

Constraint 3: adjacent nodes have different colors.
```
(1_1 => not (2_1 or 3_1)) and (1_2 => not (2_2 or 3_2)) and ... and (1_m => not (2_m or 3_m)), if node 1 is adjacent to node 2 and node 3.
...
(n_1 => not (2_1 or 3_1)) and (n_2 => not (2_2 or 3_2)) and ... and (n_m => not (2_m or 3_m)), if node n is adjacent to node 2 and node 3.
```
This problem is solved in the is_colorable() method in [script.py](script.py). Now we can solve the quantitive problem by sending queries to this function, and this step is accomplished by the method colorability() in [script.py](script.py).   

The implementation of this plan is in the method problem_2() in [script.py](script.py).  
The result of the method problem_2() in [script.py](script.py) is here:
```
The colorability of 6-node graph is: 2 colors
The colorability of 20-node graph is: 4 colors
The colorability of 50-node graph is: 6 colors
The colorability of 100-node graph is: 6 colors
```

## Problem 3 [Solving Sudoku Using SAT Solvers]
#### Question: 
Sudoku is a popular number-placement puzzle that originated in France in the end of the 19th century. Modern Sudoku was likely invented by Howard Garns from Connersville, Indiana and was first published in 1979 under the name “Number Place”. The objective of the puzzle is to place numbers 1 - 9 on a 9times9 grid, such that each number occurs only once in every row, every column, and every of the nine 3×3 sub-grids that compose the main grid. Sudoku puzzles are grids that have been partially occupied with numbers. The task is then to occupy the remaining fields in such a way that the constraints on rows, columns, and sub-grids are satisfied. A sample Sudoku problem and its solution are given in Figure 1. For more information about Sudoku refer to its Wikipedia page at http://en.wikipedia.org/wiki/Sudoku.  
This problem has two parts. In the first part, you will write the boolean constraints in mathematical notation for solving a Sudoku puzzle. In the second part, you will write code and invoke a SAT solver to solve the Sudoku instance.

### Part 1:

#### Solution: 
Similar to problem 2, we make 9*9*9 = 729 boolean variables. An variable i_j_k == true iff k is placed at row i and column j.
```
1_1_1 ... 1_1_9, 1_2_1 ... 1_2_9, ... 1_9_1 ... 1_9_9,
2_1_1 ... 2_1_9, 2_2_1 ... 2_2_9, ... 2_9_1 ... 2_9_9,
...
9_1_1 ... 9_1_9, 9_2_1 ... 9_2_9, ... 9_9_1 ... 9_9_9,
```

##### 1. Write the boolean formula for the constraints that each number can occur at most once in every row. [5 points]
The formula is:
```
for all j in [1:9], 
for all k in [1:9],  
for all i in [1:9],  
    i_j_k => not (or (i_j'_k for all j' in [1:9] such that j' != j))
    i.e.
    (assert (=> i_1_k (not (or i_2_k i_3_k ... i_9_k))))
```
The concrete result is:
```
1_1_1 => not (1_2_1 or 1_3_1 or ... or 1_9_1)
2_1_1 => not (2_2_1 or 2_3_1 or ... or 2_9_1)
...
9_1_1 => not (9_2_1 or 9_3_1 or ... or 9_9_1)
```
```
1_1_2 => not (1_2_2 or 1_3_2 or ... or 1_9_2)
2_1_2 => not (2_2_2 or 2_3_2 or ... or 2_9_2)
...
9_1_2 => not (9_2_2 or 9_3_2 or ... or 9_9_2)
```
...
```
1_1_9 => not (1_2_9 or 1_3_9 or ... or 1_9_9)
2_1_9 => not (2_2_9 or 2_3_9 or ... or 2_9_9)
...
9_1_9 => not (9_2_9 or 9_3_9 or ... or 9_9_9)
```
...
```
1_9_1 => not (1_2_1 or 1_3_1 or ... or 1_1_1)
2_9_1 => not (2_2_1 or 2_3_1 or ... or 2_1_1)
...
9_9_1 => not (9_2_1 or 9_3_1 or ... or 9_1_1)
```
```
1_9_2 => not (1_2_2 or 1_3_2 or ... or 1_1_2)
2_9_2 => not (2_2_2 or 2_3_2 or ... or 2_1_2)
...
9_9_2 => not (9_2_2 or 9_3_2 or ... or 9_1_2)
```
...
```
1_9_9 => not (1_2_9 or 1_3_9 or ... or 1_1_9)
2_9_9 => not (2_2_9 or 2_3_9 or ... or 2_1_9)
...
9_9_9 => not (9_2_9 or 9_3_9 or ... or 9_1_9)
```


##### 2. Write the boolean formula for the constraints that each number can occur at most once in every column. [5 points]. 

The formula is:
```
for all i in [1:9],  
for all k in [1:9],  
for all j in [1:9],  
    i_j_k => not (or (i'_j_k for all i' in [1:9] such that i' != i)) 
```

The concrete result is:
```
1_1_1 => not or (2_1_1 ... 9_1_1)
...
1_9_1 => not or (2_9_1 ... 9_9_1)
```
...
```
1_1_9 => not or (2_1_9 ... 9_1_9)
...
1_9_9 => not or (2_9_9 ... 9_9_9)
```
...
```
9_1_9 => not or (2_1_9 ... 1_1_9)
...
9_9_9 => not or (2_9_9 ... 1_9_9)
```


##### 3. Write the boolean formula for the constraints that each number can occur at most once in every 3×3 sub-grid.
```
for all i in [1:9],  
for all j in [1:9],  
for all k in [1:9],  
    i_j_k => not or (i'_j_'_k for all i'_j' in the same block of i_j and i'_j' != i_j)
    i.e.
    i_j_k => not or (i'_j_'_k for all i'_j' such that
                     i' in [(ceil(i/3)-1)*3+1 : (ceil(i/3)-1)*3+1+2]
                     j' in [(ceil(j/3)-1)*3+1 : (ceil(j/3)-1)*3+1+2]
                     i != i' or j != j'
                     )
    i.e.
    (assert (=> i_j_k (not (or i'_j'_k ... ))))
```
### Part 2
#### Question
Encode the above constraints in a SAT solver and solve the Sudoku instance given in Figure 1. One of the widely used techniques is to encode these constraints using the API of the SAT solver. Two popular options are as follows; 1) Using Z3 (downloadable at http://z3.codeplex.com/) and use Python API and 2) Use MiniSAT (downloadable at http: //minisat.se/) and use C++ API. Alternatively, you can write code to generate constraints in SMT-2 format (described at http://smtlib.cs.uiowa.edu) and give the SMT-2 file as an
input to the binary of SAT solver.[25 points]

![Soduku puzzle, Figure 1](https://github.com/MartinMeng008/COMP590HW2/blob/master/inputFiles/Sudoku_puzzle_figure1.png)

#### Solution
```
Step 1: make boolean variables.
Step 2: add constraints.
    2.1: each cell has at least one value
        for all i in [1:9], j in [1:9], 
            i_j_1 or i_j_2 or ... or i_j_9
            i.e.
            (assert (or i_j_1 i_j_2 ... i_j_9))
    2.2: each cell has not more than one value
        for all i in [1:9], j in [1:9], k in [1:9]
        i_j_k => not or (i_j_k') for all k' in [1:9] such that k' != k
                    (assert (=> i_j_1 (not (or i_j_2 ... i_j_9))))
    2.3: each number can occur at most once in every row
    2.4: each number can occur at most once in every column
    2.5: each number can occur at most once in every 3×3 sub-grid
Step 3: add constraint from the question (figure 1)
Step 4: check-sat and get-model
```

The implementation of this plan is in the method problem_3() in [script.py](script.py).  
The input file to z3 is [resultingFiles/input_3](resultingFiles/input_3), and z3's output file is [resultingFiles/output_3](resultingFiles/output_3), which shows the solution of the sudoku as shown in the figure below.

![Soduku solution, Figure 2](https://github.com/MartinMeng008/COMP590HW2/blob/master/resultingFiles/figure2_sudoku_solution.jpeg)



