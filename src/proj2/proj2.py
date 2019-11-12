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

    def render(self):
        return self.name


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
        super().__init__(left, right)
        self.name = "and"


class Or(BinaryExpression):
    def __init__(self, left, right):
        super().__init__(left, right)
        self.name = "or"


class Implies(BinaryExpression):
    def __init__(self, left, right):
        super().__init__(left, right)
        self.name = "=>"


class Not(UnaryExpression):
    def __init__(self, expr):
        super().__init__(expr)
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

    def v(self, i): return Literal('v_{}'.format(i))
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
        self.add_constraint(And(self.v(1), self.v(2)))
        # self.encode_tree(self.node_count)
        # self.encode_decision(self.input_count, self.node_count)

    def write_enc(self, file_name):
        smt_lib = open(file_name, "w")

        # Declare consts
        for literal in Literal.literals:
            print("(declare-const {} Bool)".format(literal), file=smt_lib)

        # Constraints
        for constraint in self.constraints:
            print("(assert {})".format(constraint.render()), file=smt_lib)

        print("(check-sat)", file=smt_lib)
        print("(get-model)", file=smt_lib)

    def print_model(self, model):
        '''prints SAT model, eventually should print the decision tree'''
        print('# === model')
#        for str_var in sorted(self.var_map.keys()):
#            v = self.var_map[str_var]
#            val = '?'
#            if v in model and model[v]:
#                val = 'T'
#            if v in model and not model[v]:
#                val = 'F'
#            print('# {}={} ({})'.format(str_var, val, v))
#        print('# === end of model')
#        print('# === tree')
#
#        for str_var in sorted(self.var_map.keys()):
#            v = self.var_map[str_var]
#            if v not in model or not model[v]:
#                continue
#
#            if re.match("^(l|r|a)", str_var):
#                index = re.findall(r'\d+', str_var)
#                print("{} {} {}".format(str_var[0], index[0], index[1]))
#
#        leaves = []
#        for i in range(2, self.node_count + 1):
#            v = self.var_map[self.v(i)]
#            if v in model and model[v]:
#                leaves.append(i)
#
#        for i in leaves:
#            v = self.var_map[self.c(i)]
#            print("c {} {}".format(i, {False: 0, True: 1}[model[v]]))
#
        print('# === end of tree')


def get_model(output):
    if not output.startswith("sat"):
        return None

    # remove break lines
    output = output[3:]
    output = output.replace("\n", "")
    output = " ".join(output.split()).split()

    stack = []
    id = 0

    def parse_s_expression():
        nonlocal output
        nonlocal stack
        nonlocal id
        if len(output) == 0:
            return []
        if not output[0].startswith("("):
            raise ValueError("S-Expression must start with an '('")
        myId = id
        stack.append(myId)
        id += 1

        output[0] = output[0][1:]
        res = []
        while len(output) != 0:
            if output[0].startswith("("):
                res.append(parse_s_expression())
                if myId not in stack:
                    return res
                continue
            if output[0][-1] == ')':
                while len(output[0]) != 0 and output[0][-1] == ')':
                    stack.pop()
                    output[0] = output[0][:-1]

                res.append(output[0])
                # pop left
                output = output[1:]
                return res
            res.append(output[0])
            # pop left
            output = output[1:]
        return res

    model = parse_s_expression()

    if len(model) == 0 or model[0] != "model":
        raise ValueError("Model retrieved is not a model.")

    values = dict()
    for fun in model[1:]:
        if not isinstance(fun, list) or len(fun) != 5 or fun[0] != "define-fun":
            raise ValueError("Found a non function definition in model.")
        name = fun[1]
        typeFun = fun[3]
        value = fun[4]
        if typeFun == "Bool":
            if value == "true":
                values[name] = True
            elif value == "false":
                values[name] = False
            else:
                values[name] = None
        elif typeFun == "Int":
            values[name] = int(value)
        elif typeFun == "Real":
            values[name] = float(value)
    return values


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
    e.write_enc(file_name)
    # print("# " + "\n# ".join(map(str, e.constraints)))
    print("# END encoded constraints")
    print("# sending to solver '" + solver + "'")

    p = subprocess.Popen(solver, shell=True, stdin=subprocess.PIPE,
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    (output, err) = p.communicate()
    print("# decoding result from solver")
    rc = p.returncode
    print(rc)
    if len(nms) == 2:
        print("# Expecting {} nodes.".format(nms[1]))
    if rc == 0:
        get_model(output.decode("UTF-8"))
    else:
        print("ERROR: something went wrong with the solver")
