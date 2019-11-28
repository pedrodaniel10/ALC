#!/usr/bin/env python3
import sys
import subprocess
import re
from expressions import *
from id3 import run_id3, get_number_nodes, get_model_id3


unsat_msg = '__UNSAT__'
solvers = {
    "CPLEX": ['minizinc', '--unsat-msg', unsat_msg,  '--solver', 'CPLEX',
              '--cplex-dll', '/opt/ibm/ILOG/CPLEX_Studio129/opl/bin/x86-64_linux/libcplex1290.so', '-'],
    "Chuffed": ['minizinc', '--unsat-msg', unsat_msg,  '--solver', 'Chuffed', '-'],
    "Geocode": ['minizinc', '--unsat-msg', unsat_msg,  '-']
}
solver = solvers["Chuffed"]


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
    def __init__(self, input_count, samples, node_count=3):
        self.samples = samples
        self.input_count = input_count
        self.node_count = node_count
        self.constraints = []

    def v(self, i): return Literal('v[{}]'.format(i))
    def l(self, i, j): return Literal('l[{},{}]'.format(i, j))
    def r(self, i, j): return Literal('r[{},{}]'.format(i, j))
    def p(self, j, i): return Literal('p[{},{}]'.format(j, i))
    def u(self, r, j): return Literal('u[{},{}]'.format(r, j))
    def d(self, sigma, r, j): return Literal('d{}[{},{}]'.format(sigma, r, j))
    def d0(self, r, j): return Literal('d0[{},{}]'.format(r, j))
    def d1(self, r, j): return Literal('d1[{},{}]'.format(r, j))
    def a(self, r, i): return Literal('a[{},{}]'.format(r, i))
    def c(self, i): return Literal('c[{}]'.format(i))
    def lamb(self, t, i): return Literal('lamb[{},{}]'.format(t, i))
    def tau(self, t, i): return Literal('tau[{},{}]'.format(t, i))

    def eq(self, q):
        '''Returns the classification of example q'''
        assert(q > 0 and q <= len(self.samples))
        return self.samples[q-1][-1]

    def eqq(self):
        '''Returns the classifications'''
        allq = []
        for i in range(len(samples)):
            allq.append(samples[i][-1])
        return allq

    def sigmaa(self):
        allsigma = []
        for sample in samples:
            allsigma.extend(sample[:-1])
        return allsigma

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
        self.add_constraint(Iff(left, right))

    def enc(self, node_count):
        '''encode the problem'''
        self.node_count = node_count
        # self.encode_tree(node_count)
        #self.encode_decision(self.input_count, self.node_count)
        # self.encode_additional_constraints(self.node_count)

    def encode_tree(self, n):
        '''Encode tree with n nodes'''
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
                    self.add_if(And(self.u(r, i), self.p(j, i)),
                                Not(self.a(r, j)))

                # 2nd part
                self.add_iff(self.u(r, j), Or(self.a(r, j), bin_recursive(
                    Or, [And(self.u(r, i), self.p(j, i)) for i in range(int(j/2), j)])))

         # Constraint 10 and 11:
         # For (10) we don't need to do the nodes n and n-1, they are leaves
         # For (11) we don't need to do the node 1, as is the root and non-leaf
        for j in range(1, n + 1):
            # Constraint 10
            if j < n - 1:
                self.add_if(Not(self.v(j)), cardinality_constraints(
                    [self.a(r, j) for r in range(1, k+1)], 1))
            # Constraint 11
            if j != 1:
                self.add_if(self.v(j), cardinality_constraints(
                    [self.a(r, j) for r in range(1, k+1)], 0))

        # Constraints 12 and 13: j can start in 2 as 1 is root (non-leaf)
        for j in range(2, n+1):
            for q in range(1, len(self.samples) + 1):
                discriminatedSamples = [
                    self.d(self.sigma(r, q), r, j) for r in range(1, k+1)]
                assert(self.eq(q) in (0, 1))
                # Constraint 13
                if self.eq(q) == 0:
                    self.add_if(And(self.v(j), self.c(j)),
                                bin_recursive(Or, discriminatedSamples))
                # Constraint 12
                if self.eq(q) == 1:
                    self.add_if(And(self.v(j), Not(self.c(j))),
                                bin_recursive(Or, discriminatedSamples))

    def encode_additional_constraints(self, n):
        # Lambda
        for i in range(1, n+1):
            # 1
            self.add_constraint(self.lamb(0, i))
            for t in range(1, int(i/2) + 1):
                # 2
                self.add_iff(self.lamb(t, i), Or(self.lamb(t, i-1),
                                                 And(self.lamb(t-1, i-1), self.v(i))))
                # Proposition 2
                self.add_if(self.lamb(t, i), And(
                    Not(self.l(i, 2*(i-t+1))), Not(self.r(i, 2*(i-t+1)+1))))

        # Tau
        for i in range(1, n+1):
            # 1
            self.add_constraint(self.tau(0, i))
            for t in range(1, int(i/2) + 2):
                # 2
                self.add_iff(self.tau(t, i), Or(self.tau(t, i-1),
                                                And(self.tau(t-1, i-1), Not(self.v(i)))))
                # Proposition 3
                self.add_if(self.tau(t, i), And(
                    Not(self.l(i, 2*(t-1))), Not(self.r(i, 2*t - 1))))

    def write_enc(self):
        encoding = ""
        # Define funcs
        encoding += B2i.definition + "\n"

        # Constraints
        for constraint in self.constraints:
            encoding += "constraint {};\n".format(constraint.render())

        # Samples
        encoding += "constraint eq ={};\n".format(self.eqq())
        encoding += "constraint samples = array2d(QLEN,FEATURES,{});\n".format(
            self.sigmaa())

        return encoding

    def print_model(self, model):
        '''prints SAT model, eventually should print the decision tree'''
        if isinstance(model, str):
            print(model)
            return

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


def enconde_run_smt(n, k, samples):
    global solver
    print("# encoding with {} nodes".format(n))

    dbg = False  # set to True if you want to see what goes into minizinc
    sol_in = ''
    sol_in += 'int: n = {};\n'.format(n)
    sol_in += 'int: k = {};\n'.format(k)
    sol_in += 'int: qlen = {};\n'.format(len(samples))  # len(samples))
    # add main.mzn to the input
    with open('main.mzn') as mf:
        sol_in += '\n' + mf.read()
    # add more constraints to sol_in if needed
    e = Enc(k, samples)
    e.enc(n)
    print("# encoded constraints to file")
    sol_in += e.write_enc()
    print("# END encoded constraints")
    # add print_model.mzn to the input
    with open('print_model.mzn') as mf:
        sol_in += '\n' + mf.read()
    if dbg:
        sys.stderr.write(sol_in)
    # run solver
    print('# run minizinc')
    p = subprocess.Popen(solver, stdin=subprocess.PIPE,
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    (po, pe) = p.communicate(input=bytes(sol_in, encoding='utf-8'))
    print('# minizinc done')
    po = str(po, encoding='utf-8')
    pe = str(pe, encoding='utf-8')
    if p.returncode != 0:
        sys.stderr.write('something went wrong with the call to {} (exit code {})'.format(
            solver, p.returncode))
        sys.stderr.write('\n>>' + '\n>>'.join(po.splitlines()))
        sys.stderr.write('\nerr>>' + '\nerr>>'.join(pe.splitlines()))
        exit(1)
    # return None if unsat
    return None if unsat_msg in po else po


if __name__ == "__main__":
    print("# reading from stdin")
    nms, samples = parse(sys.stdin)
    print("# Running id3")
    root = run_id3(samples, nms[0])
    n = get_number_nodes(root)
    model = get_model_id3(root)
    if n % 2 == 0:
        # Returns an even number of nodes (it shouldn't happen, just for precaution)
        n += 1
        model = enconde_run_smt(n, nms[0], samples)
    elif model == None:
        model = enconde_run_smt(n, nms[0], samples)

    print("# Obtained tree with {} nodes from id3".format(n))
    i = n - 2
    node_count = n
    while True:
        if node_count == 1:
            i = 3
        if i < 3:
            break
        new_model = enconde_run_smt(i, nms[0], samples)
        if new_model == None:  # => UNSAT
            print("# UNSAT {} nodes, output last SAT model".format(i))
            break
        else:
            print("# SAT {} nodes".format(i))
            node_count = i
            i -= 2
            model = new_model
            Literal.clean()

    e = Enc(nms[0], samples, node_count=node_count)
    e.print_model(model)
    print("# Model has {} nodes".format(node_count))

    if len(nms) == 2:
        print("# Expecting {} nodes.".format(nms[1]))
