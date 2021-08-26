from pathlib import Path
print('Running' if __name__ == '__main__' else 'Importing', Path(__file__).resolve())
from package.parse.parser import Parser, ParseError
from z3 import *

class PropLength(Parser):
    #given f return a tuple representing (length of f, no. of operators in f, no. of props in f, no. of different props, no. of diff operators, list of seen operators, list of seen props)
    #(len, numOp, numProp, numDiffProp, numDiffOp, seenOP, seenProp)
    def start(self):
        return self.equiv()

    def ineq(self):
        l = self.match('exp')
        while True:
            op = self.maybe_keyword('>', '<', '=', '≤', '≥')
            if op is None:
                break
            r = self.match('exp')
            if op not in r[5] and op not in l[5]:
                l[5].update(r[5])
                l[5].add(op)
                l[6].update(r[6])
                rv = (l[0]+r[0]+1, l[1]+r[1]+1, l[2]+r[2], len(l[6]), len(l[5]), l[5], l[6])
            else: #not a new operator
                l[5].update(r[5])
                l[6].update(r[6])
                rv = (l[0]+r[0]+1, l[1]+r[1]+1, l[2]+r[2], len(l[6]), len(l[5]), l[5], l[6])
            # if op == '>':
            #     rv = l > r
            # elif op == '<':
            #     rv = l < r
            # elif op == '=':
            #     rv = l == r
            # elif op == '≥':
            #     rv = l >= r
            # elif op == '≤':
            #     rv = l <= r
            # return rv
        return l

    def exp(self):
        rv = self.match('term')
        while True:
            op = self.maybe_keyword('+', '-')
            if op is None:
                break

            term = self.match('term')
            if op not in rv[5] and op not in term[5]:
                rv[5].update(term[5])
                rv[5].add(op)
                rv[6].update(term[6])
                rv = (rv[0]+term[0]+1, rv[1]+term[1]+1, rv[2]+term[2], len(rv[6]), len(rv[5]), rv[5], rv[6])
            else:
                rv[5].update(term[5])
                rv[6].update(term[6])
                rv = (rv[0]+term[0]+1, rv[1]+term[1]+1, rv[2]+term[2], len(rv[6]), len(rv[5]), rv[5], rv[6])
            # if op == '+':
            #     rv = rv + term
            # else:
            #     rv = rv - term
        return rv

    def term(self):
        rv = self.match('factor')
        while True:
            op = self.maybe_keyword('*', '/')
            if op is None:
                break
            term = self.match('factor')
            if op not in rv[5] and op not in term[5]:
                rv[5].update(term[5])
                rv[5].add(op)
                rv[6].update(term[6])
                rv = (rv[0]+term[0]+1, rv[1]+term[1]+1, rv[2]+term[2], len(rv[6]), len(rv[5]), rv[5], rv[6])
            else:
                rv[5].update(term[5])
                rv[6].update(term[6])
                rv = (rv[0]+term[0]+1, rv[1]+term[1]+1, rv[2]+term[2], len(rv[6]), len(rv[5]), rv[5], rv[6])
            # if op == '*':
            #     rv = rv + term
            # else:
            #     rv = rv + term
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
            seenProp = set()
            seenProp.add(rv)
            return (1, 0, 1, 1, 0, set(), seenProp)
        except ParseError:
            chars.append(self.char('0-9'))
            rv = int(''.join(chars))
            return (1, 0, 0, 0, 0, set(), set())

    def lit(self):
        if self.maybe_keyword('('):
            rv = self.match('equiv')
            self.keyword(')')
            return rv
        prevPos = self.pos
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
        seenProp = set()
        seenProp.add(rv)
        return (1, 0, 1, 1, 0, set(), seenProp)
    
    def neg(self):
        if self.maybe_keyword('¬'):
            l = self.match('lit')
            if '¬' not in l[5]:
                #seenOp = set()
                l[5].add('¬')
                rv = (1+l[0], 1+l[1], l[2], len(l[6]), len(l[5]), l[5], l[6])
            else:
                rv = (1+l[0], 1+l[1], l[2], len(l[6]), len(l[5]), l[5], l[6])
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
            l[5].update(r[5])
            l[5].add('∨')
            l[6].update(r[6])
            rv = (l[0]+r[0]+1, l[1]+r[1]+1, l[2]+r[2], len(l[6]), len(l[5]), l[5], l[6])
            return rv
        return l

    def conj(self):
        l = self.match('neg')
        if self.maybe_keyword('∧'):
            r = self.match('conj')
            if r is None:
                return None
            l[5].update(r[5])
            l[5].add('∧')
            l[6].update(r[6])
            rv = (l[0]+r[0]+1, l[1]+r[1]+1, l[2]+r[2], len(l[6]), len(l[5]), l[5], l[6])
            return rv
        return l

    def impl(self):
        l = self.match('disj')
        if self.maybe_keyword('→'):
            r = self.match('impl')
            if r is None:
                return None
            l[5].update(r[5])
            l[5].add('→')
            l[6].update(r[6])
            rv = (l[0]+r[0]+1, l[1]+r[1]+1, l[2]+r[2], len(l[6]), len(l[5]), l[5], l[6])
            return rv
        return l

    def equiv(self):
        l = self.match('impl')
        if self.maybe_keyword('↔'):
            r = self.match('equiv')
            if r is None:
                return None
            l[5].update(r[5])
            l[5].add('↔')
            l[6].update(r[6])
            rv = (l[0]+r[0]+1, l[1]+r[1]+1, l[2]+r[2], len(l[6]), len(l[5]), l[5], l[6])
            return rv
        return l
