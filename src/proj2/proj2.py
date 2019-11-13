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


class Int:
    def __init__(self, value):
        self.value = value

    def render(self):
        return str(self.value)


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


class Sum(BinaryExpression):
    def __init__(self, left, right):
        super().__init__(left, right)
        self.name = "+"


class Equals(BinaryExpression):
    def __init__(self, left, right):
        super().__init__(left, right)
        self.name = "="


class Not(UnaryExpression):
    def __init__(self, expr):
        super().__init__(expr)
        self.name = "not"


class B2i(UnaryExpression):
    definition = "(define-fun b2i ((b Bool)) Int (ite b 1 0))"

    def __init__(self, expr):
        super().__init__(expr)
        self.name = "b2i"


def lr(i, n):
    assert(i <= n)
    return set(filter(lambda x: x % 2 == 0 and abs(i - x) >= 1, [j for j in range(i + 1, min(2 * i, n - 1)+1)]))


def rr(i, n):
    assert(i <= n)
    return set(filter(lambda x: x % 2 != 0 and abs(i - x) >= 2, [j for j in range(i + 2, min(2 * i + 1, n)+1)]))


def cardinality_constraints(expr, result):
    def sum_recursive(expr):
        assert(len(expr) > 0)
        if len(expr) == 1:
            return B2i(expr[0])
        return Sum(B2i(expr[0]), sum_recursive(expr[1:]))

    return Equals(sum_recursive(expr), Int(result))


def bin_recursive(Bin, expr):
    assert(len(expr) > 0)
    if len(expr) == 1:
        return expr[0]
    return Bin(expr[0], bin_recursive(Bin, expr[1:]))


class Enc:
    def __init__(self, input_count, samples):
        self.samples = samples
        self.input_count = input_count
        self.constraints = []

    def v(self, i): return Literal('v_{}'.format(i))
    def l(self, i, j): return Literal('l_{}_{}'.format(i, j))
    def r(self, i, j): return Literal('r_{}_{}'.format(i, j))
    def p(self, j, i): return Literal('p_{}_{}'.format(j, i))
    def s(self, i): return Literal('s_{}'.format(i))
    def u(self, r, j): return Literal('u_{}_{}'.format(r, j))
    def d(self, sigma, r, j): return Literal('d{}_{}_{}'.format(sigma, r, j))
    def d0(self, r, j): return Literal('d0_{}_{}'.format(r, j))
    def d1(self, r, j): return Literal('d1_{}_{}'.format(r, j))
    def a(self, r, i): return Literal('a_{}_{}'.format(r, i))
    def c(self, i): return Literal('c_{}'.format(i))
    def lamb(self, t, i): return Literal('ulamb_{}_{}'.format(t, i))
    def tau(self, t, i): return Literal('tau_{}_{}'.format(t, i))

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

    def add_if(self, left, right):
        '''add iff constraint between left and right'''
        self.add_constraint(Implies(left, right))

    def add_iff(self, left, right):
        '''add iff constraint between left and right'''
        self.add_constraint(Implies(left, right))
        self.add_constraint(Implies(right, left))

    def enc(self, node_count):
        '''encode the problem'''
        self.node_count = node_count
        self.encode_tree(node_count)
        self.encode_decision(self.input_count, self.node_count)
        self.encode_additional_constraints(self.node_count)

    def encode_tree(self, n):
        # Constraint 1: ~v1
        self.add_constraint(Not(self.v(1)))

        # vn and vn-1 are leaves
        self.add_constraint(self.v(n))
        self.add_constraint(self.v(n-1))

        # Constraint 2: vi => -lij
        # No need to do for v1 as from (1), v1 is never a leaf
        for i in range(2, n + 1):
            for j in lr(i, n):
                self.add_if(self.v(i), Not(self.l(i, j)))

        # Constraint 3: lij <=> rij+1
        for i in range(1, n + 1):
            for j in lr(i, n):
                self.add_iff(self.l(i, j), self.r(i, j+1))

        # Constraint 4: sum_{j in LR(i)} lij = 1
        # No need to do for i = n-1 and i = n-2, as both nodes are necessarily leaves
        for i in range(1, n - 1):
            literals = [self.l(i, j) for j in lr(i, n)]
            self.add_constraint(
                Implies(Not(self.v(i)), cardinality_constraints(literals, 1)))

        # Constraint 5: pji <=> lij, pji <=> rij
        # No need to do for i = n-1 and i = n-2, as both nodes are necessarily leaves
        for i in range(1, n - 1):
            for j in lr(i, n):
                self.add_iff(self.p(j, i), self.l(i, j))
            for j in rr(i, n):
                self.add_iff(self.p(j, i), self.r(i, j))

        # Constraint 6: sum_{j/2}^{min(j-1, N)}
        for j in range(2, n + 1):
            literals = []
            for i in range(int(j/2), min(j - 1, n) + 1):
                literals.append(self.p(j, i))
            self.add_constraint(cardinality_constraints(literals, 1))

    def discriminateFeature(self, d, branch, children, k, n):
        '''This function will make the constraints (7) or (8) depending 
           on parameters given.'''
        for r in range(1, k+1):
            for j in range(2, n + 1):
                ands = []
                for i in range(int(j/2), j):
                    ands.append(And(self.p(j, i), d(r, i)))
                    ands.append(And(self.a(r, i), branch(i, j)))

                self.add_iff(d(r, j), bin_recursive(Or, ands))
            self.add_constraint(Not(d(r, 1)))

        for j in range(2, n + 1):
            for i in range(int(j/2), j):
                childrens = children(i, n)
                # lij/rij that don't exist are false
                if j not in childrens:
                    self.add_constraint(Not(branch(i, j)))

    def encode_decision(self, k, n):
        '''This will encode the decision (constraints 7 to 13)'''
        # Constraint 7:
        self.discriminateFeature(self.d0, self.r, rr, k, n)

        # Constraint 8:
        self.discriminateFeature(self.d1, self.l, lr, k, n)

         # Constrain 9:
        for j in range(1, n + 1):
            for r in range(1, k + 1):
                for i in range(int(j/2), j):
                    # 1st part: 
                    self.add_if(And(self.u(r,i), self.p(j,i)), Not(self.a(r,j)))

                # 2nd part
                self.add_iff(self.u(r,j), Or(self.a(r,j), bin_recursive(Or, [And(self.u(r,i), self.p(j,i)) for i in range(int(j/2), j)])))

        # Constraint 10 and 11:
        # For (10) we don't need to do the nodes n and n-1, they are leaves
        # For (11) we don't need to do the node 1, as is the root and non-leaf
        for j in range(1, n + 1):
            # Constraint 10
            if j < n - 1:
                self.add_if(Not(self.v(j)), cardinality_constraints([self.a(r, j) for r in range(1, k+1)], 1))
            # Constraint 11
            if j != 1:
                self.add_if(self.v(j), cardinality_constraints([self.a(r, j) for r in range(1, k+1)], 0))

        # Constraints 12 and 13: j can start in 2 as 1 is root (non-leaf)
        for j in range(2, n+1):
            for q in range(1, len(self.samples) + 1):
                discriminatedSamples = [self.d(self.sigma(r, q), r, j) for r in range(1, k+1)]
                assert(self.eq(q) in (0, 1))
                # Constraint 13
                if self.eq(q) == 0:
                    self.add_if(And(self.v(j), self.c(j)), bin_recursive(Or, discriminatedSamples))
                # Constraint 12
                if self.eq(q) == 1:
                    self.add_if(And(self.v(j), Not(self.c(j))), bin_recursive(Or, discriminatedSamples))

    def encode_additional_constraints(self, n):
        # Lambda
        for i in range(1, n+1):
            # 1
            self.add_constraint(self.lamb(0,i))
            for t in range(1, int(i/2) + 1):
                # 2
                self.add_iff(self.lamb(t,i), Or(self.lamb(t,i-1), And(self.lamb(t-1,i-1), self.v(i))))
                # Proposition 2
                self.add_if(self.lamb(t,i), And(Not(self.l(i,2*(i-t+1))), Not(self.r(i,2*(i-t+1)+1))))

        # Tau
        for i in range(1, n+1):
            # 1
            self.add_constraint(self.tau(0,i))
            for t in range(1, int(i/2) + 2):
                # 2
                self.add_iff(self.tau(t,i), Or(self.tau(t,i-1), And(self.tau(t-1,i-1), Not(self.v(i)))))
                # Proposition 2
                self.add_if(self.tau(t,i), And(Not(self.l(i,2*(t-1))), Not(self.r(i,2*t - 1))))

    def write_enc(self, file_name):
        smt_lib = open(file_name, "w")

        # Define funcs
        print(B2i.definition, file=smt_lib)

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
        for str_var in sorted(model.keys()):
            val = '?'
            if model[str_var]:
                val = 'T'
            if not model[str_var]:
                val = 'F'
            print('# {} = {}'.format(str_var, val))
        print('# === end of model')
        print('# === tree')

        for str_var in sorted(model.keys()):
            if model[str_var] and re.match("^(l|r|a)", str_var):
                index = re.findall(r'\d+', str_var)
                if str_var[0] in ("l", "r") and int(index[0]) >= int(index[1]):
                    continue
                print("{} {} {}".format(str_var[0], index[0], index[1]))

        leaves = []
        for i in range(2, self.node_count + 1):
            v = self.v(i).render()
            if v in model and model[v]:
                leaves.append(i)

        for i in leaves:
            v = self.c(i).render()
            if v not in model:
                print("c {} {}".format(i, self.eq(1)))
            else:
                print("c {} {}".format(i, {False: 0, True: 1}[model[v]]))

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
    e.enc(nms[1])
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
    if len(nms) == 2:
        print("# Expecting {} nodes.".format(nms[1]))
    if rc == 0:
        e.print_model(get_model(output.decode("UTF-8")))
    else:
        print("ERROR: something went wrong with the solver")
