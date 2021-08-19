from pathlib import Path
# from project.package import propParser
print('Running' if __name__ == '__main__' else 'Importing', Path(__file__).resolve())
import z3
from z3 import *
import string

global listOfOperators
# global EQ_OPERATORS
# EQ_OPERATORS = ['=', '>', '<', '≤', '≥']
s = Solver()

import sys
current_module = sys.modules[__name__]


# strFormula in SMT 2.0 format
def mainResult(strFormula, operators):
    global listOfOperators
    listOfOperators = operators
    z3_exp = parse_smt2_string(strFormula)[0]
    conc(z3_exp, s)
    listOfAllOper = []
    for l in listOfOperators:
        listOfAllOper.extend(l)
    formulas = getFormulas(getModels(), z3_exp)
    result = getFormulasFormatted(formulas)
    #result.extend(parenCombFormatted(parenComb(strFormula, listOfAllOper)))
    print(result)
    #what does children() return whn z3 exp has no children? 

def numConc(s):
    global listOfOperators
    for index,listOp in enumerate(listOfOperators):
        if str(s) in listOp:
            return len(listOp)
    return 1

    
def numOfConcretizations(z3_exp):
    res = 1
    if z3_exp != None:
        res *= numConc(z3_exp.decl())
    return res

var = string.ascii_lowercase
global idx 
idx = 0
def freshVariable():
    global idx
    res = var[idx]
    idx += 1
    return Int(res)

def getRightChild(z3_exp):
    children = z3_exp.children()
    if len(children) == 0:
        return None
    elif len(children) == 1:
        return None
    else:
        return children[1]

def getLeftChild(z3_exp):
    children = z3_exp.children()
    if len(children) == 0:
        return None
    else:
        return children[0]
    
def conc(z3_exp, solver):
    if z3_exp != None:
        conc(getLeftChild(z3_exp), solver)
        global listOfOperators
        rootVal = z3_exp.decl()
        for l in listOfOperators:
            if str(rootVal) in l:
                x = freshVariable()
                numConc = numOfConcretizations(z3_exp)
                
                solver.add(0<=x, x<numConc)
                # if abstractedTree != None:
                #     conc(abstractedTree.getLeftChild(), solver)
                #     conc(abstractedTree.getRightChild(), solver)
                conc(getRightChild(z3_exp), solver)

def getModels():
    result = []
    while s.check() == sat:
        m = s.model()
        dict = {}
        for d in m:
            dict[str(d)] = m[d]
        result.append(dict)
        # Create a new constraint the blocks the current model
        block = []
        for d in m:
            # d is a declaration
            if d.arity() > 0:
                raise Z3Exception("uninterpreted functions are not supported")
            # create a constant from declaration
            c = d()
            if is_array(c) or c.sort().kind() == Z3_UNINTERPRETED_SORT:
                raise Z3Exception("arrays and uninterpreted sorts are not supported")
            block.append(c != m[d])
        s.add(Or(block))
    #print(result)
    return result

global modelIdx
def getFormulas(listOfModels, z3_exp):
    result = []
    for l in listOfModels:
        global modelIdx
        modelIdx = 0
        # list = getFormula(l, z3_exp)
        # formula = " ".join(list)
        formula = getFormula(l, z3_exp)
        if formula != None:
            result.append(formula)
    return result

def getFormula(model, z3_exp): 
    global modelIdx
    #x = var[modelIdx]
    formula = None
    if z3_exp != None:
        leftF = getFormula(model, getLeftChild(z3_exp))
        rootVal = z3_exp.decl()
        if str(rootVal) == 'Int' or len(z3_exp.children()) == 0: # or is_int(rootVal) or is_real(rootVal) or is_bool(rootVal):
            rootVal = z3_exp
        global listOfOperators
        matched = False
        for listOp in listOfOperators:
            if str(rootVal) in listOp:
                idx = model[(var[modelIdx])].as_long()
                rv = listOp[idx]
                modelIdx += 1
                matched = True
        rightF = getFormula(model, getRightChild(z3_exp))
        
        if leftF is not None:
            if not matched:
                formula = joinFormulasZ3(str(rootVal), leftF, rightF) #getattr(current_module, rootVal)(leftF, rightF)
            else:
                formula = joinFormulasZ3(str(rv), leftF, rightF) #getattr(current_module, rv)(leftF, rightF)
        else:
            if not matched:
                formula = rootVal
            else:
                formula = rv
    return formula

def joinFormulasZ3(op, leftF, rightF):
    formula = None
    try:
        formula = getattr(current_module, op)(leftF, rightF)
    except AttributeError:
        if op == '+':
            formula = leftF + rightF
        elif op == '-':
            formula = leftF - rightF
        elif op == '*':
            formula = leftF * rightF
        elif op == '/':
            formula = leftF / rightF
        elif op == '==':
            formula = leftF == rightF
        elif op == '<':
            formula = leftF < rightF
        elif op == '>':
            formula = leftF > rightF
        elif op == '>=':
            formula = leftF >= rightF
        elif op == '<=':
            formula = leftF <= rightF
        elif op == '!=':
            formula = leftF != rightF
        elif op == '=':
            formula = leftF != rightF
        elif op == '**':
            formula = leftF ** rightF
        elif op == '%':
            formula = leftF % rightF
    return formula


def getFormulasFormatted(flist):
    result = []
    #diffList = listDiff(flist, 0, 1)
    for index,z3_exp in enumerate(flist):
        valid = checkValid(z3_exp)
        sat = checkSat(z3_exp)
        #diff = diffList[index]
        result.append(" ".join([str(z3_exp), valid, sat])) #, str(diff)]))
    return result

def checkSat(z3_exp):
    solver = Solver()
    solver.add(z3_exp)
    return str(solver.check())

def checkValid(z3_exp):
    solver = Solver()
    solver.add(Not(z3_exp))
    if solver.check() == unsat:
        return 'valid'
    return 'invalid'

exp1 = '(declare-const x Int) (assert (=> (> x 1) (> x 0)))'

mainResult(exp1, [['Implies', '=='], ['>', '<','=']])
# maybe I can make this a string then bring it back to z3? How?

z3_exp = parse_smt2_string(exp1)[0]
x1 = z3_exp.children()[0].children()[0]
one1 = z3_exp.children()[0].children()[1]
#formula = x1 > one1
print(len(x1.children()))
print(len(one1.children()))
print(is_bool(Bool('P')))
print(is_bool(Or(Bool('P'), Bool('Q'))))
#print(formula)

# exp2 = Implies(Int('x') > 1, Int('x') > 0)
# v = parse_smt2_string('(declare-const x Int) (assert (=> (> x 1) (> x 0)))')
# x1 = v[0].children()[0].children()[0]
# one1 = v[0].children()[0].children()[1]
# print(x1 > one1)
# print('howdy')
# print(exp2.children())
# print(exp2.decl())
# print(v[0])
# testList = [And, Or, Implies]
# varList = [Bool('P'), Bool('Q')]
# print(testList[0](varList[0], varList[1]))
# exp5 = Not(Bool('P'))
# #print(Bool('R')(None, None))
# #exp6 = And(Bool('P'))
# x = Int('x')
# exp7 = (x > 1) == (x > 0)
# print(checkSat(exp7))
# import operator
# print(operator.gt(2,4))


# import sys
# current_module = sys.modules['z3']
# #print(sys.modules) 
# # z3_exp1 = getattr(current_module, 'Implies')(x > 1, x > 2)
# # z3_exp1 = getattr(current_module, 'gt')(x, 2)
# # print(z3_exp1)
# one = 1
# #print(one.decl())
# ast1 = exp7.children()[0].children()[0]
# print(eq(ast1, Int('x')))
# exp8 = x > 1
# so = Solver()
# #so.add(exp8)
# so.add(x1 > one1)
# print(so.check())
