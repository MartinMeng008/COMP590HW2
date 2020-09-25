# HW2
Author: Martin Meng

This is the repository for HW2 of UNC's COMP 590: Program Verification and Synthesis.

The file 'script.py' contains the code for all questions.
The directory "resultingFiles" contains the output of the script.

## Problem 1

### 1.1
Question: There is a basket containing an apple, a banana, a cherry and a date. Four children named Erica, Frank, Greg and Hank are each to be given a piece of the fruit.
```
(a) Erica likes cherries and dates. 
(b) Frank likes apples and cherries.
(c) Greg likes bananas and cherries.
(d) Hank likes apples , bananas , and dates.
```
We have 4 kids and 4 fruits. Every kid likes 2 to 3 kinds of fruits.

    Step 1: make constants for kids and fruits.
    Step 2: add constraints that formulate.
        2.1: if a kid chooses one fruit, then she cannot choose another.
            e.g. (assert (=> (= (like Erica) apple) (not (or (= (like Erica) banana) (= (like Erica) cherry) (= (like Erica) date)))))
        2.2: if a fruit is chosen by a kid, then it cannot be choosen by other kids.
            e.g. (assert (=> (= (like Erica) apple) (not (or (= (like Frank) apple) (= (like Greg) apple) (= (like Hank) apple)))))
    Step 3: add kids' preference.
        e.g. (assert (or (= (like Erica) cherry) (= (like Erica) date)))
    Step 4: check sat and get model.

The result file is shown in resultingFiles/output\_1\_1. It says that one possible assignment is: 
```
Erica gets date
Frank gets apple
Greg gets cherry
Hank gets banana
```

### 1.2
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

The result is here:
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
  (define-fun is\_Ted\_guilty () Bool
    true)
  (define-fun is\_Fred\_guilty () Bool
    false)
  (define-fun is\_Ed\_guilty () Bool
    true)
)
```

## Problem 2

### 2.1 Graph of 6 nodes

