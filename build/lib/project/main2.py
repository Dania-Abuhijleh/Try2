from pathlib import Path
print('Running' if __name__ == '__main__' else 'Importing', Path(__file__).resolve())
import z3
from z3 import *
import string
import click
import ast
from main import FormulaGenLEANsyntax
from FormulaGenerator import FormulaGenerator

#global listOfOperators
# global EQ_OPERATORS
# EQ_OPERATORS = ['=', '>', '<', '≤', '≥']
s = Solver()

import sys
current_module = sys.modules[__name__]


#TODO move the cmd line func out and let it call the class
@click.command()
@click.argument('filepath', type=click.Path(exists=True))
def generateFromFile(filepath):
    """
    Call mainResult with the parameters in the file at the given path.
        
    :param filepath: The path to the file.
    :type filepath: String

    :param listOfOperators: The list of lists of operators
    :type listOfOperators: list
    """
    with open(filepath, 'r', encoding='utf-8-sig') as f:
        formula = f.readline()
        operators = ast.literal_eval(f.readline())
        # print(formula)
        # print(operators)
        formulaGen = FormulaGenerator(str(formula), operators)
        #self.mainResult(str(formula), operators)
        formulaGen.mainResult()
        # try:
        #     mainResult(str(formula), operators)
        # except Exception:
        #     mainResultOne(formula, operators)
        try:
            formulaGen.mainResult()
        except Exception:
            formulaLEANGen = FormulaGenLEANsyntax(str(formula), operators)
            formulaLEANGen.mainResultOne()


# def generateFromStr(strFormula, operators):
#     try:
#         formulaGen = FormulaGenerator(str(strFormula), operators)
#         formulaGen.mainResult()
#     except Exception:
#         formulaLEANGen = FormulaGenLEANsyntax(str(strFormula), operators)
#         formulaLEANGen.mainResultOne()



exp1 = '(declare-const x Int) (assert (=> (> x 1) (> x 0)))'
#mainResult(exp1, [['Implies', '=='], ['>','<','==']])
exp2 = '(declare-const P Bool) (declare-const Q Bool) (assert (= (= P Q) (and (=> P Q) (=> Q P))))'
#mainResult(exp2, [['Implies', '=='], ['And', 'Or'], ['Not']]) #TODO: Not isn't being applied
exp3 = '(declare-const x Int) (declare-const y Int) (assert (= (+ (+ x y) 1) (+ x (+ y 1))))'
# mainResult(exp3, [['==', '!='], ['+', '-']])
# maybe I can make this a string then bring it back to z3? How?

# plus = Function('plus', IntSort(), IntSort(), IntSort())
# minus = Function('minus', IntSort(), IntSort(), IntSort())
exp4 = '(declare-fun plus (Int Int) Int) (declare-fun minus (Int Int) Int) (declare-const x Int) (declare-const y Int) (declare-const z Int) (assert (= (plus x (plus y z)) (plus (plus x y) z)))'
formulaGen = FormulaGenerator(strFormula=exp3, listOfOperators=[['==', '!='], ['+', '-']])
formulaGen.mainResult() #mainResult(exp4, [['plus', 'minus']])
#so transitive thing doesn't happen [['Implies', '=='], ['>','<','=='], ['==', 'Or']] 
# probably because the model is computed first before replacement begins (concretization)

z3_exp = parse_smt2_string(exp1)[0]
x1 = z3_exp.children()[0].children()[0]
one1 = z3_exp.children()[0].children()[1]
#formula = x1 > one1
# print(len(x1.children()))
# print(len(one1.children()))
# print(is_bool(Bool('P')))
# print(is_bool(Or(Bool('P'), Bool('Q'))))
#print(formula)

if __name__ == "__main__":  #TODO: uncomment
    generateFromFile()

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