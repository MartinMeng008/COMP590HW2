#! /anaconda3/bin/python

import os
from z3 import *

def problem_1_1():
    sorts = ['Kid', 'Fruit']
    kids = ['Erica', 'Frank', 'Greg', 'Hank']
    fruits = ['apple', 'banana', 'cherry', 'date']
    kids_prefered_fruits = {
                             'Erica' : ['cherry', 'date'],
                             'Frank' : ['apple', 'cherry'],
                             'Greg' : ['banana', 'cherry'],
                             'Hank' : ['apple', 'banana', 'date']
                           }
    with open('resultingFiles/input_1_1', 'w') as f:

        # Step 1: make constants for kids and fruits, create a like function. 
        for sort in sorts:
            f.write('(declare-sort %s)\n' % sort)
        for kid in kids:
            f.write('(declare-const %s Kid)\n' % kid)
        for fruit in fruits:
            f.write('(declare-const %s Fruit)\n' % fruit)
        f.write('(declare-fun like (Kid) Fruit)\n')
        f.write('\n')

        # Step 2: add constraints that formulate:

        # step 2.1: if a kid chooses one fruit, then she cannot choose another.
        for kid in kids:
            for fruit in fruits:
                stmt = '(assert (=> (= (like %s) %s) (not (or' % (kid, fruit) 
                for another_fruit in fruits:
                    if another_fruit != fruit:
                        stmt += ' (= (like %s) %s)' % (kid, another_fruit)
                stmt += '))))\n'
                f.write(stmt)
        f.write('\n')

        # step 2.2: if a fruit is chosen by a kid, then it cannot be choosen by other kids. 
        for fruit in fruits:
            for kid in kids:
                stmt = '(assert (=> (= (like %s) %s) (not (or' % (kid, fruit)
                for another_kid in kids:
                    if another_kid != kid:
                        stmt += ' (= (like %s) %s)' % (another_kid, fruit)
                stmt += '))))\n'  
                f.write(stmt)
        f.write('\n')

        # Step 3: add kids' preference.
        for kid in kids:
            stmt = '(assert (or'
            for fruit in kids_prefered_fruits[kid]:
                stmt += ' (= (like %s) %s)' % (kid, fruit)            
            stmt += '))\n'
            f.write(stmt)
        f.write('\n')

        # Step 4: check sat and get model.
        f.write('(check-sat)\n')
        f.write('(get-model)\n')
        

    os.system('z3 -smt2 resultingFiles/input_1_1 > resultingFiles/output_1_1')

def setup():
    os.system('rm -rf resultingFiles')
    os.system('mkdir resultingFiles')

def main():
    setup()
    problem_1_1()

if __name__ == '__main__':
    main()
