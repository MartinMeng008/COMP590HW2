#! /anaconda3/bin/python

import os
from z3 import *

def is_colorable(nodes, adjacent_list, num_colors):
    # return whether this graph is colorable with the given number of colors

    num_nodes = len(nodes)
    vars_list = [] 
    with open('resultingFiles/input_2_%i' % num_nodes, 'w') as f:

        # Step 1: make boolean variables.
        for i in range(num_nodes):
            curr_var_list = []
            for j in range(num_colors):
                s = 'n%i_%i' % (i, j)
                curr_var_list.append(s)
                f.write('(declare-const %s Bool)\n' % s)
            vars_list.append(curr_var_list)
        f.write('\n')

        # Step 2: each node has at least one color.
        for node in range(num_nodes):
            stmt = '(assert (or'
            for color in range (num_colors):
                stmt += ' n%i_%i' % (node, color)
            stmt += '))\n'
            f.write(stmt) 
        f.write('\n')          

        # Step 3: each node has a unique color.
        for i in range(num_nodes):
            for j in range(num_colors):
                stmt = '(assert (=> n%i_%i (not (or' % (i, j)
                for color in range(num_colors):
                    if color != j:
                        stmt += ' n%i_%i' % (i, color)
                stmt += '))))\n'
                f.write(stmt) 
        f.write('\n')

        # Step 4: adjacent nodes have different colors.
        for color in range(num_colors):
            for edge in adjacent_list:
                f.write('(assert (=> n%i_%i (not n%i_%i)))\n' % (edge[0], color, edge[1], color))

        f.write('\n')

        # Step 5: solve the model.
        f.write('(check-sat)\n')
        f.write('(get-model)\n')

    os.system('z3 -smt2 resultingFiles/input_2_%i > resultingFiles/output_2_%i' % (num_nodes, num_nodes))
    
def checkColorabilitySat(num_nodes):
    with open('resultingFiles/output_2_%i' % num_nodes, 'r') as f:
        s = f.readline().rstrip()
        return s == 'sat'

def colorability(nodes, adjacent_list):
    num_colors = 1
    num_nodes = len(nodes)
    sat = False
    while (not sat):
        is_colorable(nodes, adjacent_list, num_colors)
        sat = checkColorabilitySat(num_nodes)
        num_colors += 1
    return num_colors - 1

def read_graph_input_file(filename):
    with open(filename) as f:
        nodes = list(map(lambda x: int(x), f.readline().rstrip().strip('[]').split(',')))
        edges = f.readline().rstrip().strip('[]').split(',')
        edges = list(map(lambda x: int(x), [x.strip().strip('()') for x in edges]))
        new_edges = []
        for i in range(0, len(edges), 2):
            new_edges.append(tuple((edges[i], edges[i+1])))
        return nodes, new_edges

def problem_2():
    num_nodes = [6, 20, 50, 100]
    for num in num_nodes:
        nodes, edges = read_graph_input_file('inputFiles/size%i.txt' % num)
        colors = colorability(nodes, edges)
        print('The colorability of %i-node graph is: %i colors' % (num, colors))

def problem_1_2():
    people = ['Ed', 'Fred', 'Ted']
    consts = ['is_%s_guilty' % person for person in people]

    with open('resultingFiles/input_1_2', 'w') as f:

        # Step 1: make boolean variables for each person.
        for const in consts:
            f.write('(declare-const %s Bool)\n' % const) 
        f.write('\n')
        
        # Step 2: add the constraint for each person.
        f.write('(assert (=> (not is_Ed_guilty) (and is_Fred_guilty (not is_Ted_guilty))))\n')
        f.write('(assert (=> (not is_Fred_guilty) (and is_Ed_guilty is_Ted_guilty)))\n')
        f.write('(assert (=> (not is_Ted_guilty) (or is_Ed_guilty is_Fred_guilty)))\n')

        # Step 3: check sat and get model.
        f.write('(check-sat)\n')
        f.write('(get-model)\n')
        
    os.system('z3 -smt2 resultingFiles/input_1_2 > resultingFiles/output_1_2')

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
    problem_1_2()
    problem_2()

if __name__ == '__main__':
    main()
