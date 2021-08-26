from pathlib import Path
print('Running' if __name__ == '__main__' else 'Importing', Path(__file__).resolve())
from package.parse.parser import Parser, ParseError
from z3 import *

class PropParser(Parser):
    def start(self):
        # try:
            rv = self.equiv()
        #     self.assert_end()
        # except ParseError:
        #     rv = self.ineq()
            return rv

    def ineq(self):
        l = self.match('exp')
        while True:
            op = self.maybe_keyword('>', '<', '=', '≤', '≥')
            if op is None:
                break
            r = self.match('exp')
            if op == '>':
                rv = l > r
            elif op == '<':
                rv = l < r
            elif op == '=':
                rv = l == r
            elif op == '≥':
                rv = l >= r
            elif op == '≤':
                rv = l <= r
            return rv
        return l

    def exp(self):
        rv = self.match('term')
        while True:
            op = self.maybe_keyword('+', '-')
            if op is None:
                break

            term = self.match('term')
            if op == '+':
                rv = rv + term #Int(rv) + Int(term)
            else:
                rv = rv - term #Int(rv) - Int(term)
        return rv

    def term(self):
        rv = self.match('factor')
        while True:
            op = self.maybe_keyword('*', '/')
            if op is None:
                break
            term = self.match('factor')
            if op == '*':
                rv = rv * term #Int(rv) * Int(term)
            else:
                rv = rv / term #Int(rv) / Int(term)
        return rv
    
    def factor(self):
        if self.maybe_keyword('('):
            rv = self.match('exp') #TODO: should this be equiv or exp??
            self.keyword(')')
            return rv
    #     elif self.maybe_keyword('¬'):
    #         rv = self.match('variable')
    #         rv = Not(rv)
    #         return rv
        return self.match('number')

    def number(self):
        chars = []
        try:
            chars.append(self.char('A-Za-z')) #removed 0-9 we don't want numbers as variables!
            while True:
                char = self.maybe_char('A-Za-z0-9')
                if char is None:
                    break
                chars.append(char)
            rv = ''.join(chars)
            return Int(rv)
        except ParseError:
            chars.append(self.char('0-9'))
            rv = int(''.join(chars))
            return rv

    def lit(self):
        # ADDED THIS start
        # prevPos = self.pos
        # try:
        #     rv = self.match('ineq')
        #     return rv
        # except ParseError:
        #     self.pos = prevPos
        # TILL HERE end
        prevPos = self.pos
        if self.maybe_keyword('('):
            rv = self.match('equiv')
            self.keyword(')')
            # ADDED THIS start
            if self.maybe_keyword('+','-','*','/','=','>','<', '≤', '≥'): #TODO: add leq <= and geq >=
                self.pos = prevPos
                return None
            # TILL HERE end
            return rv
        prevPos = self.pos #and added this
        chars = []
        try:
            chars.append(self.char('A-Za-z')) #TODO: then return None if this is an exception???
        except ParseError:
            return None
        while True:
            char = self.maybe_char('A-Za-z')
            if char is None:
                break
            chars.append(char)
        if self.maybe_keyword('+','-','*','/','=','>','<', '≤', '≥'): #TODO: add leq <= and geq >=
            self.pos = prevPos
            return None
        rv = ''.join(chars)
        return Bool(rv)
    
    def neg(self):
        if self.maybe_keyword('¬'):
            l = self.match('lit')
            rv = Not(l)
            return rv
        #return self.match('lit')
        l = self.match('lit')
        if l is None:
            l = self.match('ineq')
        return l

    def disj(self):
        l = self.match('conj')
        if self.maybe_keyword('∨'):
            r = self.match('disj')
            if r is None:
                return None
            rv = Or(l, r)
            return rv
        return l

    def conj(self):
        l = self.match('neg')
        if self.maybe_keyword('∧'):
            r = self.match('conj')
            if r is None:
                return None
            rv = And(l, r)
            return rv
        return l

    def impl(self):
        l = self.match('disj')
        if self.maybe_keyword('→'):
            r = self.match('impl')
            if r is None:
                return None
            rv = Implies(l, r)
            return rv
        return l

    def equiv(self):
        l = self.match('impl')
        if self.maybe_keyword('↔'):
            r = self.match('equiv')
            if r is None:
                return None
            rv = l == r
            return rv
        return l
