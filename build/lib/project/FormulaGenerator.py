import z3
from z3 import *
import string

s = Solver()

import sys
current_module = sys.modules[__name__]

class FormulaGenerator:
    """
    Generate a list of formulas from the given formula.
    Operators in the formula will be substitited by operators in same lists from the given list of lists of operators.
    
    :param strFormula: The base formula.
    :type strFormula: String
    """
    def __init__(self, listOfOperators, strFormula):
        self.listOfOperators = listOfOperators
        self.strFormula = strFormula
        self.idx = 0
        self.var = string.ascii_lowercase
        self.modelIdx = 0


    def parseListofListOp(self, lop):
        """
        Parse the list of lists of operators into z3 format, return the parsed list.
        
        :param lop: The list of lists of operators to parse.
        :type lop: list
        """
        result = []
        for list in lop:
            result.append(self.parseListOp(list))
        return result

    def parseListOp(self, l):
        """
        Parse a list of operators into z3 format
        
        :param l: The list of operators to parse.
        :type l: list
        """
        result = []
        for op in l:
            if op == '=>' or op == '→' or op.lower() == 'implies':
                result.append('Implies')
            elif op == '<=>' or op == '↔' or op.lower() == 'equiv':
                result.append('==')
            elif op == '∧' or op.lower() == 'and':
                result.append('And')
            elif op == '∨' or op.lower() == 'or':
                result.append('Or')
            elif op == '¬' or op.lower() == 'not':
                result.append('Not')
            elif op == '=' or op.lower() == 'equal':
                result.append('==')
            else:
                result.append(op)
        

    # strFormula in SMT 2.0 format
    def mainResult(self): #, strFormula, operators):
        """
        Return a list of formulas similar to the given formula
        
        :param strFormula: The base formula used to generate similar formulas.
        :type strFormula: String

        :param operators: The list of lists of operators to replace. If two operateros are in the same list then they are replacable with each other.
        :type operators: list
        """
        #global listOfOperators
        #listOfOperators = operators
        z3_exp = parse_smt2_string(self.strFormula)[0]
        self.conc(z3_exp, s)
        listOfAllOper = []
        for l in self.listOfOperators:
            listOfAllOper.extend(l)
        formulas = self.getFormulas(self.getModels(), z3_exp)
        result = self.getFormulasFormatted(formulas)
        #result.extend(parenCombFormatted(parenComb(strFormula, listOfAllOper)))
        print(result)
        #what does children() return when z3 exp has no children? 

    def numConc(self, s):
        #global listOfOperators
        for index,listOp in enumerate(self.listOfOperators):
            if str(s) in listOp:
                return len(listOp)
        return 1

    
    def numOfConcretizations(self, z3_exp):
        res = 1
        if z3_exp != None:
            res *= self.numConc(z3_exp.decl())
        return res

    #var = string.ascii_lowercase
    # global idx 
    # idx = 0
    def freshVariable(self):
        # global idx
        res = self.var[self.idx]
        self.idx += 1
        return Int(res)

    def getRightChild(self, z3_exp):
        children = z3_exp.children()
        if len(children) == 0:
            return None
        elif len(children) == 1:
            return None
        else:
            return children[1]

    def getLeftChild(self, z3_exp):
        children = z3_exp.children()
        if len(children) == 0:
            return None
        else:
            return children[0]
    
    def conc(self, z3_exp, solver):
        if z3_exp != None:
            self.conc(self.getLeftChild(z3_exp), solver)
            #global listOfOperators
            rootVal = z3_exp.decl()
            for l in self.listOfOperators:
                if str(rootVal) in l:
                    x = self.freshVariable()
                    numConc = self.numOfConcretizations(z3_exp)
                    
                    solver.add(0<=x, x<numConc)
                    # if abstractedTree != None:
                    #     conc(abstractedTree.getLeftChild(), solver)
                    #     conc(abstractedTree.getRightChild(), solver)
                    self.conc(self.getRightChild(z3_exp), solver)

    def getModels(self):
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

    #global modelIdx
    def getFormulas(self, listOfModels, z3_exp):
        result = []
        for l in listOfModels:
            #global modelIdx
            self.modelIdx = 0
            # list = getFormula(l, z3_exp)
            # formula = " ".join(list)
            formula = self.getFormula(l, z3_exp)
            if formula != None:
                result.append(formula)
        return result

    def getFormula(self, model, z3_exp): 
        #global modelIdx
        #x = var[modelIdx]
        formula = None
        if z3_exp != None:
            leftF = self.getFormula(model, self.getLeftChild(z3_exp))
            rootVal = z3_exp.decl()
            if str(rootVal) == 'Int' or len(z3_exp.children()) == 0: # or is_int(rootVal) or is_real(rootVal) or is_bool(rootVal):
                rootVal = z3_exp
            #global listOfOperators
            matched = False
            for listOp in self.listOfOperators:
                if str(rootVal) in listOp:
                    idx = model[(self.var[self.modelIdx])].as_long()
                    rv = listOp[idx]
                    self.modelIdx += 1
                    matched = True
            rightF = self.getFormula(model, self.getRightChild(z3_exp))
            
            if leftF is not None:
                if not matched:
                    formula = self.joinFormulasZ3(str(rootVal), leftF, rightF) #getattr(current_module, rootVal)(leftF, rightF)
                else:
                    formula = self.joinFormulasZ3(str(rv), leftF, rightF) #getattr(current_module, rv)(leftF, rightF)
            else:
                if not matched:
                    formula = rootVal
                else:
                    formula = rv
        return formula

    def joinFormulasZ3(self, op, leftF, rightF):
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
            # elif op == '=':
            #     formula = leftF = rightF
            elif op == '**':
                formula = leftF ** rightF
            elif op == '%':
                formula = leftF % rightF
        return formula


    def getFormulasFormatted(self, flist):
        result = []
        #diffList = listDiff(flist, 0, 1)
        for index,z3_exp in enumerate(flist):
            valid = self.checkValid(z3_exp)
            sat = self.checkSat(z3_exp)
            #diff = diffList[index]
            result.append(" ".join([str(z3_exp), valid, sat])) #TODO:, str(diff)]))
        return result

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
