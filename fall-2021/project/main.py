from pathlib import Path
# from project.package import propParser
print('Running' if __name__ == '__main__' else 'Importing', Path(__file__).resolve())
# insert root formula and operators to consider
# then abstract the formula
# then produce all permutations of the abstracted formula by changing operators
# can I use z3 for this by abstracting operators into unknown functions (like f represents and, or) then enumerate all models and reconstruct formula for each model?
from typing import List, Set
import builtins
builtins.Z3_LIB_DIRS = ['C:/Users/dania/AppData/Local/Programs/Python/Python39/Lib/site-packages/z3/lib/libz3.dll']
import z3
from z3 import *
from pythonds.basic import Stack
from pythonds.trees import BinaryTree
import operator
import string
#import propParser
#from .parseTree import ParseTree
from package.parseTree import ParseTree
from package.propParser import PropParser
from package.parseFormula import PropLength
from package.parse.parser import ParseError
import click
import ast


global listOfOperators
global EQ_OPERATORS
EQ_OPERATORS = ['=', '>', '<', '≤', '≥']

@click.command()
@click.argument('filepath', type=click.Path(exists=True))
def main(filepath):
    with open(filepath, 'r', encoding='utf-8-sig') as f:
        formula = f.readline()
        operators = ast.literal_eval(f.readline())
        print(formula)
        print(operators)
        #mainResultOne(formula, operators)
        fGenLean = FormulaGenLEANsyntax(listOfOperators=operators, strFormula=formula)
        fGenLean.mainResultOne()

#take in list of lists of operators
# @click.command()
# @click.argument('strFormula')
# @click.argument('operators', type=List)

class FormulaGenLEANsyntax:
    def __init__(self, listOfOperators, strFormula):
        self.listOfOperators = listOfOperators
        self.strFormula = strFormula
        self.idx = 0
        self.var = string.ascii_lowercase
        self.modelIdx = 0
        self.EQ_OPERATORS = ['=', '>', '<', '≤', '≥']
        self.s = Solver()

    def mainResultOne(self): #,strFormula, operators):
        #click.echo('Enter the formula as a string and a list of lists of operators')
        #global listOfOperators
        #listOfOperators = operators
        parser = ParseTree()
        pt = parser.parse(self.strFormula)
        print(pt)
        self.absTree(pt)
        self.conc(pt, self.s)
        #print(postorder(pt))
        listOfAllOper = []
        for l in self.listOfOperators:
            listOfAllOper.extend(l)
        #print(getModels())
        # result = getFormulas(getModels(), pt)
        formulas = self.getFormulas(self.getModels(), pt)
        result = self.getFormulasFormatted(formulas)
        result.extend(self.parenCombFormatted(self.parenComb(self.strFormula, listOfAllOper)))
        print(result)

# def buildParseTree(fpexp):
#     fplist = fpexp.split()
#     pStack = Stack()
#     eTree = BinaryTree('')
#     pStack.push(eTree)
#     currentTree = eTree

#     for i in fplist:
#         if i == '(':
#             currentTree.insertLeft('')
#             pStack.push(currentTree)
#             currentTree = currentTree.getLeftChild()

#         elif i in ['∧', '∨', '→', '↔']:
#             currentTree.setRootVal(i)
#             currentTree.insertRight('')
#             pStack.push(currentTree)
#             currentTree = currentTree.getRightChild()

#         elif i == ')':
#             currentTree = pStack.pop()

#         elif i not in ['∧', '∨', '→', '↔']:
#             try:
#                 currentTree.setRootVal(i)
#                 parent = pStack.pop()
#                 currentTree = parent

#             except ValueError:
#                 raise ValueError("token '{}' is not a valid integer".format(i))
#     return eTree

    def postorder(self, tree):
        if tree != None:
            self.postorder(tree.getLeftChild())
            self.postorder(tree.getRightChild())
            print(tree.getRootVal())

    def absTree(self,tree):
        if tree != None:
            self.absTree(tree.getLeftChild())
            self.absTree(tree.getRightChild())
            global listOfOperators
            rootVal = tree.getRootVal()
            for index,listOp in enumerate(self.listOfOperators):
                if rootVal in listOp:
                    tree.setRootVal('t' + str(index))
                    break

    def numConc(self, s):
        global listOfOperators
        for index,listOp in enumerate(self.listOfOperators):
            if s == 't' + str(index):
                return len(listOp)
        return 1

    def numOfConcretizations(self, abstractedTree):
        res = 1
        if abstractedTree != None:
            res *= self.numConc(abstractedTree.getRootVal())
        return res

    # var = string.ascii_lowercase
    # global idx 
    # idx = 0
    def freshVariable(self):
        global idx
        res = self.var[self.idx]
        self.idx += 1
        return Int(res)


    
    def conc(self, abstractedTree, solver):
        if abstractedTree != None:
            self.conc(abstractedTree.getLeftChild(), solver)
            global listOfOperators
            rootVal = abstractedTree.getRootVal()
            for index in range(len(self.listOfOperators)):
                if rootVal == 't' + str(index):
                    x = self.freshVariable()
                    numConc = self.numOfConcretizations(abstractedTree)
                    
                    solver.add(0<=x, x<numConc)
                    # if abstractedTree != None:
                    #     conc(abstractedTree.getLeftChild(), solver)
                    #     conc(abstractedTree.getRightChild(), solver)
                    self.conc(abstractedTree.getRightChild(), solver)

    def getModels(self):
        result = []
        while self.s.check() == sat:
            m = self.s.model()
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
            self.s.add(Or(block))
        #print(result)
        return result


    # global modelIdx
    def getFormulas(self, listOfModels, abstractedTree):
        result = []
        #print(listOfModels)
        for l in listOfModels:
            #print(l)
        #for i in range(len(var)):
            #global modelIdx
            self.modelIdx = 0
            list = self.getFormula(l, abstractedTree)
            formula = " ".join(list)
            result.append(formula)
            # parser = PropParser()
            # z3_exp = parser.parse(formula)
            # # print(z3_exp)
            # valid = checkValid(z3_exp)
            # sat = checkSat(z3_exp)
            # #result.append(" ".join(list))
            # result.append(" ".join([formula, valid, sat]))
        return result

    def getFormulasFormatted(self, flist):
        result = []
        diffList = self.listDiff(flist, 0, 1)
        for index,formula in enumerate(flist):
            parser = PropParser()
            z3_exp = parser.parse(formula)
            valid = self.checkValid(z3_exp)
            sat = self.checkSat(z3_exp)
            diff = diffList[index]
            result.append(" ".join([formula, valid, sat, str(diff)]))
        return result



    def getFormula(self, model, abstractedTree): 
        #print(model) 
        formula = []
        #i = 0
        #global modelIdx
        x = self.var[self.modelIdx] #x = var[i]
        # print("x: ")
        # print(x)
        # print("model: ")
        # print(model[Int(x)])
        if abstractedTree != None:
            formula.extend(self.getFormula(model, abstractedTree.getLeftChild()))
            rootVal = abstractedTree.getRootVal()
            global listOfOperators
            matched = False
            for index,listOp in enumerate(self.listOfOperators):
                if rootVal == 't' + str(index):
                    # print(Int(var[modelIdx]))
                    # idx = model[Int(var[modelIdx])].as_long()
                    idx = model[(self.var[self.modelIdx])].as_long()
                    formula.append(listOp[idx])
                    self.modelIdx += 1
                    matched = True
            if not matched:
                formula.append(abstractedTree.getRootVal())
            formula.extend(self.getFormula(model, abstractedTree.getRightChild()))
        return formula

    def getFormula(self, model, abstractedTree):  
        formula = []
        #global modelIdx
        x = self.var[self.modelIdx]
        if abstractedTree != None:
            formula.extend(self.getFormula(model, abstractedTree.getLeftChild()))
            rootVal = abstractedTree.getRootVal()
            #global listOfOperators
            matched = False
            for index,listOp in enumerate(self.listOfOperators):
                if rootVal == 't' + str(index):
                    # print(Int(var[modelIdx]))
                    # idx = model[Int(var[modelIdx])].as_long()
                    idx = model[(self.var[self.modelIdx])].as_long()
                    formula.append(listOp[idx])
                    self.modelIdx += 1
                    matched = True
            if not matched:
                formula.append(abstractedTree.getRootVal())
            formula.extend(self.getFormula(model, abstractedTree.getRightChild()))
        return formula

    def checkSat(self, z3_exp):
        solver = Solver()
        solver.add(z3_exp)
        return str(solver.check())

    def checkValid(self, z3_exp):
        solver = Solver()
        solver.add(Not(z3_exp))
        if solver.check() == unsat:
            return 'valid'
        return 'invalid'


# def allParenPlacement(f, operators):
#     #first remove existing brackets
#     f.replace(')', '')
#     f.replace('(', '')
#     n = 0
#     for o in operators:
#         n += f.count(o)
#     n = n/2
#     combList = listParens([], 0, n, 0, 0, [])

# def listParens(l, pos, n, open, close, res):
#     if(close == n):
#         # l = []
#         # for i in l:
#         #     res.append(i)
#         # res.append(l)
#         # return res
#         for i in l:
#             print(i, end = "")
#         print()
#         return
#     else:
#         if(open > close):
#             l[pos] = ')'
#             listParens(l, pos + 1, n, open, close + 1, res)
#         if(open < n):
#             l[pos] = '('
#             listParens(l, pos + 1, n, open + 1, close, res)


    def parenComb(self, formula, allOperators):
        f = formula.replace(')', '')
        f = f.replace('(', '')
        listf = f.split()
        res = []
        global EQ_OPERATORS
        for i in range(0, len(f)):
            if f[i] not in allOperators and f[i] != ' ' and f[i] != ')':
                for j in range(i+1, len(f)):
                    if f[j] in EQ_OPERATORS:
                            break
                    if f[j] not in allOperators and f[j] != ' ' and f[j] != '(':
                        str = f[:i] + '(' + f[i:j+1] + ')' + f[j+1:]
                        res.append(str)
        return res

    def parenCombFormatted(self, flist):
        result = []
        parser = PropParser()
        for f in flist:
            try:
                z3_exp = parser.parse(f)
            except ParseError:
                print(f)
                break
            #print(z3_exp)
            valid = self.checkValid(z3_exp)
            sat = self.checkSat(z3_exp)
            result.append(" ".join([f, valid, sat]))
        return result

    def syntacticDifficulty(self, formula):
        parser = PropLength() #TODO: What to consider? # of props, # of operations, 
        diffTuple = parser.parse(formula)
        #(len, numOp, numProp, numDiffProp, numDiffOp, seenOP, seenProp)
        res = 0.2*diffTuple[0] + 0.1*diffTuple[1] + 0.1*diffTuple[2] + 0.3*diffTuple[3] + 0.3*diffTuple[4]
        return res

    def listDiff(self, flist, minRange, maxRange):
        diffs = []
        res = []
        for f in flist:
            diffs.append(self.syntacticDifficulty(f))
        maxD = max(diffs)
        minD = 0
        for d in diffs:
            r = (maxRange - minRange) * ((d - minD)/(maxD - minD)) + minRange
            res.append(r)
        return res



#print(parenComb('5 * 3 / 2 - 4', ['*', '/', '-']))
#print(listParens([''] * 2 * 2, 0, 2, 0, 0, []))
#     strList = str.split()
#     v1 = Bool('v1')
#     v2 = Bool('v2')
#     for s in strList:
#         if s == '∨':
#             v1 = Or(v1, v2)
#         elif s == '∧':
#             v1 = And(v1, v2)
#         elif s == '→'

#abs('(P ∨ P) ↔ P')

# if __name__ == "__main__":  #TODO: uncomment
#     main()

# print(z3.__file__)

fGenLean = FormulaGenLEANsyntax(listOfOperators=[['∨', '∧'], ['→', '↔']], strFormula='P ∨ P ↔ P')
fGenLean.mainResultOne()

# S = set(('P'))
# print(S)
# S.add('U')
# print(S)
# S1 = set(('P'))
# S2 = set(('Q', 'P'))
# S1.update(S2)
# print(S1)
# S = set()
# S.add('P')
# print(S)
# parser = PropLength() #TODO: What to consider? # of props, # of operations, 
# p = parser.parse('P ∨ ¬Q ∨ R ↔ P') #(8, 4, 4, 3, 3, {'∨', '¬', '↔'}, {'R', 'P', 'Q'})
# print(p)
# print(syntacticDifficulty('P ∨ ¬Q ∨ R ↔ P'))
#(len, numOp, numProp, numDiffProp, numDiffOp, seenOP, seenProp)

#main(r"C:\Users\dania\Documents\college\Fall2021Co-op\fall-2021\test.txt")
#mainResult('(P ↔ Q) ↔ ((P → Q) ∧ (Q → P))', [['∨', '∧'], ['→', '↔'], ['¬']])
#mainResult('(x + y) + 1 = x + (y + 1)', [['+', '-'], ['=']]) #TODO: Parse Error
#mainResult('P ∨ ¬Q ∨ P ↔ P', [['∨', '∧'], ['→', '↔'], ['¬']])
#mainResult('P ∨ P ↔ P', [['∨', '∧'], ['→', '↔']])
#mainResult('x > 1 → x > 0', [['>', '<'], ['→', '↔']])
# sf = Solver()
# exp = (Int('x') < 1) == (Int('x') > 0)
# exp2 = Implies(Int('x') > 1, Int('x') > 0)
# exp3 = Not(Implies(Int('x') > 1, Int('x') > 0))
# parser = PropParser()
# exp4 = parser.parse('x > 1 → x > 0')
# print(checkSat(exp))
# print(checkValid(exp))
# print(exp2)
# print(checkValid(exp2))
# print(checkSat(exp3))
# print(exp4)
# print(checkValid(exp4))
# print(prove(exp2 == exp4))

# sf.add(exp)
# print(sf.check())
# print(exp)

# parser = ParseTree()
# pt = parser.parse('P ∨ P ↔ P')
# print(pt)
# #pt = buildParseTree("( ( P ∨ P ) ↔ P )")
# #pt = buildParseTree("( ( ( P → P ) → P ) → P )") 
# #pt = buildParseTree("( ( ( P → Q ) → P ) → ( x > 0 ) )") 
# pt.postorder() 
# absTree(pt)
# pt.postorder()

# conc(pt, s)
# print(s)
# print(s.check())
# print(numOfConcretizations(pt))
# #print(getModels())
# print(getFormulas(getModels(), pt))
# #print(getModels().sort())
