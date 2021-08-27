import unittest
# from project.main import FormulaGenLEANsyntax
# from project.FormulaGenerator import FormulaGenerator
# from project import *
#from project.main import FormulaGenerator
#from project import main
#from ..project.main import *
from main import FormulaGenLEANsyntax

class FormulaGenTestCase(unittest.TestCase):

    def setUp(self):
        self.formulaGen = FormulaGenLEANsyntax(listOfOperators=[['∨', '∧'], ['→', '↔']], strFormula='P ∨ P ↔ P')

    def test_p_or_p(self):
        """Test P or P implies P"""

        result = self.formulaGen.mainResultOne()
        self.assertEqual(result, [' P  ∨  P  →  P  valid sat 1.0', ' P  ∧  P  ↔  P  valid sat 1.0', ' P  ∧  P  →  P  valid sat 1.0', ' P  ∨  P  ↔  P  valid sat 1.0', '(P ∨ P) ↔ P valid sat', '(P ∨ P ↔ P) valid sat', 'P ∨ (P ↔ P) valid sat'])

if __name__ == '__main__':
    unittest.main()
