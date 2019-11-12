#!/usr/bin/env python3
import sys
import subprocess
import re

file_name = "smt_lib"
solver = ['z3']
args = [file_name]
solver.extend(args)
solver = " ".join(solver)

class Literal:
    literals = set()

    def __init__(self, name):
        self.name = name
        Literal.literals.add(name)

class BinaryExpression:
    def __init__(self, left, right):
        self.left = left
        self.right = right
        self.name = ""
    
    def render(self):
        return "({} {} {})".format(self.name, self.left.render(), self.right.render())

class UnaryExpression:
    def __init__(self, expr):
        self.expr = expr
        self.name = ""
    
    def render(self):
        return "({} {})".format(self.name, self.expr.render())

class And(BinaryExpression):
    def __init__(self, left, right):
        super(left,right)
        self.name = "and"

class Or(BinaryExpression):
    def __init__(self, left, right):
        super(left,right)
        self.name = "or"

class Implies(BinaryExpression):
    def __init__(self, left, right):
        super(left,right)
        self.name = "=>"

class Not(UnaryExpression):
    def __init__(self, expr):
        super(expr)
        self.name = "not"
        
def lr(i, n):
    assert(i <= n)
    return set(filter(lambda x: x % 2 == 0 and abs(i - x) >= 1, [j for j in range(i + 1, min(2 * i, n - 1)+1)]))

def rr(i, n):
    assert(i <= n)
    return set(filter(lambda x: x % 2 != 0 and abs(i - x) >= 2, [j for j in range(i + 2, min(2 * i + 1, n)+1)]))

class Enc:
    def __init__(self, input_count, samples):
        self.samples = samples
        self.input_count = input_count
        self.constraints = []

    def v(self, i): return Literal('v_{}'.format(i)))
    def l(self, i, j): return Literal('l_{},{}'.format(i, j))
    def r(self, i, j): return Literal('r_{},{}'.format(i, j))
    def p(self, j, i): return Literal('p_{},{}'.format(j, i))
    def s(self, i): return Literal('s_{}'.format(i))
    def u(self, r, j): return Literal('u_{},{}'.format(r, j))
    def d(self, sigma, r, j): return Literal('d{}_{},{}'.format(sigma, r, j))
    def d0(self, r, j): return Literal('d0_{},{}'.format(r, j))
    def d1(self, r, j): return Literal('d1_{},{}'.format(r, j))
    def a(self, r, i): return Literal('a_{},{}'.format(r, i))
    def c(self, i): return Literal('c_{}'.format(i))

    def eq(self, q):
        '''Returns the classification of example q'''
        assert(q > 0 and q <= len(self.samples))
        return self.samples[q-1][-1]

    def sigma(self, r, q):
        '''Returns fr value for example q'''
        assert(r > 0 and r <= self.input_count)
        assert(q > 0 and q <= len(self.samples))
        return self.samples[q-1][r-1]

    def add_constraint(self, constraint):
        '''add constraints, which is a list of literals'''
        self.constraints.append(constraint)

    def enc(self):
        '''encode the problem'''
        print("")
        #self.encode_tree(self.node_count)
        #self.encode_decision(self.input_count, self.node_count)


    def print_model(self, model):
        '''prints SAT model, eventually should print the decision tree'''
        print('# === model')
        for str_var in sorted(self.var_map.keys()):
            v = self.var_map[str_var]
            val = '?'
            if v in model and model[v]:
                val = 'T'
            if v in model and not model[v]:
                val = 'F'
            print('# {}={} ({})'.format(str_var, val, v))
        print('# === end of model')
        print('# === tree')

        for str_var in sorted(self.var_map.keys()):
            v = self.var_map[str_var]
            if v not in model or not model[v]:
                continue

            if re.match("^(l|r|a)", str_var):
                index = re.findall(r'\d+', str_var)
                print("{} {} {}".format(str_var[0], index[0], index[1]))

        leaves = []
        for i in range(2, self.node_count + 1):
            v = self.var_map[self.v(i)]
            if v in model and model[v]:
                leaves.append(i)

        for i in leaves:
            v = self.var_map[self.c(i)]
            print("c {} {}".format(i, {False: 0, True: 1}[model[v]]))

        print('# === end of tree')


def get_model(lns):
    vals = dict()
    found = False
    for l in lns:
        l = l.rstrip()
        if not l:
            continue
        if not l.startswith('v ') and not l.startswith('V '):
            continue
        found = True
        vs = l.split()[1:]
        for v in vs:
            if v == '0':
                break
            vals[int(var(v))] = not sign(v)
    return vals if found else None


def parse(f):
    nms = None
    samples = []
    for l in f:
        s = l.rstrip().split()
        if not s:
            continue
        if nms:
            samples.append([int(l) for l in s])
        else:
            nms = [int(l) for l in s]
    return (nms, samples)


if __name__ == "__main__":
    print("# reading from stdin")
    nms, samples = parse(sys.stdin)
    print("# encoding")
    e = Enc(nms[0], samples)
    e.enc()
    print("# encoded constraints")
    #print("# " + "\n# ".join(map(str, e.constraints)))
    print("# END encoded constraints")
    print("# sending to solver '" + solver + "'")

    p = subprocess.Popen(solver, shell=True, stdin=subprocess.PIPE,
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    (output, err) = p.communicate()
    print("# decoding result from solver")
    rc = p.returncode
    print(output.decode("UTF-8"))
    if len(nms) == 2:
        print("# Expecting {} nodes.".format(nms[1]))
    if rc == 10:
        e.print_model(get_model(lns))
    elif rc == 20:
        print("UNSAT")
    else:
        print("ERROR: something went wrong with the solver")
