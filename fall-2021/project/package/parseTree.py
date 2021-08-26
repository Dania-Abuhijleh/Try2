from pathlib import Path
print('Running' if __name__ == '__main__' else 'Importing', Path(__file__).resolve())

from package.parse.parser import Parser, ParseError
from typing import Set
from pythonds.basic import Stack
from pythonds.trees import BinaryTree

#turn python string expression into binary tree representation, string can be flexible paranthesis optional.
#add support for mathematical propositions (x>1 -> x>0)
class ParseTree(Parser):
    def start(self):
        return self.equiv()

    
    def lit(self):
        # ADDED THIS start
        prevPos = self.pos
        try:
            rv = self.match('ineq')
            return rv
        except ParseError:
            self.pos = prevPos
        # TILL HERE end
        if self.maybe_keyword('('):
            rv = self.match('equiv')
            self.keyword(')')
            return rv
        prevPos = self.pos
        chars = []
        chars.append(self.char('A-Za-z'))
        while True:
            char = self.maybe_char('A-Za-z')
            if char is None:
                break
            chars.append(char)
        if self.maybe_keyword('+','-','*','/','=','>','<', '≤', '≥'):
            self.pos = prevPos
            return None
        rv = BinaryTree('')
        rv.setRootVal(''.join(chars))
        rv.insertLeft('')
        rv.insertRight('')
        return rv
    
    def neg(self):
        if self.maybe_keyword('¬'):
            l = self.match('lit')
            rv = BinaryTree('')
            rv.setRootVal('¬')
            rv.insertLeft('')
            rv.insertRight(l) #TODO:should this be None or ''?
            return rv
        #return self.match('lit')
        rv = self.match('lit')
        if rv is None:
            rv = self.match('ineq')
        return rv

    def disj(self):
        l = self.match('conj')
        if self.maybe_keyword('∨'):
            r = self.match('disj')
            if r is None:
                return None
            rv = BinaryTree('')
            rv.setRootVal('∨')
            rv.insertLeft(l)
            rv.insertRight(r)
            return rv
        return l

    def conj(self):
        l = self.match('neg')
        if self.maybe_keyword('∧'):
            r = self.match('conj')
            if r is None:
                return None
            rv = BinaryTree('')
            rv.setRootVal('∧')
            rv.insertLeft(l)
            rv.insertRight(r)
            return rv
        return l

    def impl(self):
        l = self.match('disj')
        if self.maybe_keyword('→'):
            r = self.match('impl')
            if r is None:
                return None
            rv = BinaryTree('')
            rv.setRootVal('→')
            rv.insertLeft(l)
            rv.insertRight(r)
            return rv
        return l

    def equiv(self):
        l = self.match('impl')
        if self.maybe_keyword('↔'):
            r = self.match('equiv')
            if r is None:
                return None
            rv = BinaryTree('')
            rv.setRootVal('↔')
            rv.insertLeft(l)
            rv.insertRight(r)
            return rv
        return l

    def ineq(self):
        l = self.match('exp')
        while True:
            op = self.maybe_keyword('>', '<', '=', '≤', '≥')
            if op is None:
                break
            r = self.match('exp')
            rv = BinaryTree('')
            rv.setRootVal(op)
            rv.insertLeft(l)
            rv.insertRight(r)
            return rv
        return l

    def exp(self):
        l = self.match('term')
        while True:
            op = self.maybe_keyword('+', '-')
            if op is None:
                break

            r = self.match('term')
            rv = BinaryTree('')
            if op == '+':
                rv.setRootVal('+')
                rv.insertLeft(l)
                rv.insertRight(r)
                return rv
            else:
                rv.setRootVal('+')
                rv.insertLeft(l)
                rv.insertRight(r)
                return rv
        return l

    def term(self):
        l = self.match('factor')
        while True:
            op = self.maybe_keyword('*', '/')
            if op is None:
                break
            r = self.match('factor')
            rv = BinaryTree('')
            if op == '*':
                rv.setRootVal('*')
                rv.insertLeft(l)
                rv.insertRight(r)
                return rv
            else:
                rv.setRootVal('/')
                rv.insertLeft(l)
                rv.insertRight(r)
                return rv
        return l
    
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
        chars.append(self.char('A-Za-z0-9'))
        while True:
            char = self.maybe_char('A-Za-z0-9')
            if char is None:
                break
            chars.append(char)
        rv = BinaryTree('')
        rv.setRootVal(''.join(chars))
        rv.insertLeft('')
        rv.insertRight('')
        return rv
    
