#!/usr/bin/env python3
import sys
import subprocess
import re
import os

file_name = "smt_lib"
solver = ['z3']
args = [file_name]
solver.extend(args)
solver = " ".join(solver)

def neg(l): return l[1:] if l[0] == '-' else '-'+l
def var(l): return l[1:] if l[0] == '-' else l
def sign(l): return l[0] == '-'

def lr(i, n):
    assert(i <= n)
    return set(filter(lambda x: x % 2 == 0 and abs(i - x) >= 1, [j for j in range(i + 1, min(2 * i, n - 1)+1)]))

def rr(i, n):
    assert(i <= n)
    return set(filter(lambda x: x % 2 != 0 and abs(i - x) >= 2, [j for j in range(i + 2, min(2 * i + 1, n)+1)]))

class Enc:
    def __init__(self, input_count, samples):
        self.fresh = 0
        self.samples = samples
        self.input_count = input_count
        self.constraints = []

    def v(self, i): return 'v_{}'.format(i)
    def l(self, i, j): return 'l_{},{}'.format(i, j)
    def r(self, i, j): return 'r_{},{}'.format(i, j)
    def p(self, j, i): return 'p_{},{}'.format(j, i)
    def s(self, i): return 's_{}'.format(i)
    def u(self, r, j): return 'u_{},{}'.format(r, j)
    def d(self, sigma, r, j): return 'd{}_{},{}'.format(sigma, r, j)
    def d0(self, r, j): return 'd0_{},{}'.format(r, j)
    def d1(self, r, j): return 'd1_{},{}'.format(r, j)
    def a(self, r, i): return 'a_{},{}'.format(r, i)
    def c(self, i): return 'c_{}'.format(i)

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

    def mk_fresh(self, nm):
        '''make fresh variable'''
        self.fresh = self.fresh + 1
        return '_' + nm + '__' + str(self.fresh)

    def mk_and(self, l1, l2):
        '''encode and between l1 and l2 by introducing a fresh variable'''
        r = self.mk_fresh(l1+'_and_'+l2)
        self.constraints.append([neg(l1), neg(l2), r])
        self.constraints.append([l1, neg(r)])
        self.constraints.append([l2, neg(r)])
        return r

    def add_iff(self, l1, l2):
        '''add iff constraint between l1 and l2'''
        self.constraints.append([neg(l1), l2])
        self.constraints.append([l1, neg(l2)])

    def add_if(self, l1, l2):
        '''add if constraint between l1 and l2'''
        self.constraints.append([neg(l1), l2])

    def mk_cnf(self, print_comments):
        '''encode constraints as CNF in DIMACS'''
        maxid = 0
        self.var_map = dict()
        cs = 0
        rv = ''
        for c in self.constraints:
            if not isinstance(c, list):
                continue
            cs = cs + 1
            for l in c:
                if var(l) not in self.var_map:
                    maxid = maxid + 1
                    self.var_map[var(l)] = maxid

        rv += 'p cnf {} {}'.format(len(self.var_map), cs) + '\n'
        for c in self.constraints:
            if isinstance(c, list):
                if print_comments:
                    rv += 'c ' + str(c) + '\n'
                rv += ' '.join(map(str, [-(self.var_map[var(l)])
                                         if sign(l) else self.var_map[l] for l in c])) + ' 0\n'
            else:
                if print_comments:
                    rv += 'c ' + str(c) + '\n'

        return rv

    def add_cardinality_constraint(self, literals):
        ''' SINZ, 2005: <=k(x1, ... , xn) for k = 1'''
        n = len(literals)
        if n == 1:
            return

        # s0 doesn't exist, is just there for indexation be simpler
        aux_vars = ["s0"]
        for i in range(1, n + 1):
            aux_vars.append(self.mk_fresh(self.s(i)))
        # -x1 | s1
        self.add_constraint([neg(literals[0]), aux_vars[1]])
        # -xn | -sn-1
        self.add_constraint([neg(literals[n-1]), neg(aux_vars[n-1])])

        # 1 < i < n
        # (-xi | si) & (-si-1 | si) & (-xi | -si-1)
        for i in range(2, n):
            self.add_constraint([neg(literals[i-1]), aux_vars[i]])
            self.add_constraint([neg(aux_vars[i-1]), aux_vars[i]])
            self.add_constraint([neg(literals[i-1]), neg(aux_vars[i-1])])

    def enc(self):
        '''encode the problem'''
        self.encode_tree(self.node_count)
        self.encode_decision(self.input_count, self.node_count)

    def encode_tree(self, n):
        '''Encode tree with n nodes'''
        # Constraint 1: -v1
        self.add_constraint([neg(self.v(1))])

        # vn and vn-1 are leaves
        self.add_constraint([self.v(n)])
        self.add_constraint([self.v(n-1)])

        # Constraint 2: vi => -lij
        # No need to do for v1 as from (1), v1 is never a leaf
        for i in range(2, n + 1):
            for j in lr(i, n):
                self.add_if(self.v(i), neg(self.l(i, j)))

        # Constraint 3: lij <=> rij+1
        for i in range(1, n + 1):
            for j in lr(i, n):
                self.add_iff(self.l(i, j), self.r(i, j+1))

        # Constraint 4: sum_{j in LR(i)} lij = 1
        # No need to do for i = n-1 and i = n-2, as both nodes are necessarily leaves
        for i in range(1, n - 1):
            literals = [self.l(i, j) for j in lr(i, n)]
            self.add_cardinality_constraint(literals)
            # -vi => one of the literals must be true
            self.add_constraint([self.v(i)] + literals)

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
            self.add_cardinality_constraint(literals)
            # one of the literals must be true
            self.add_constraint(literals)

    def discriminateFeature(self, d, branch, children, k, n):
        '''This function will make the constraints (7) or (8) depending 
           on parameters given.'''
        for r in range(1, k+1):
            for j in range(2, n + 1):
                ands = []
                for i in range(int(j/2), j):
                    ands.append(self.mk_and(self.p(j, i), d(r, i)))
                    ands.append(self.mk_and(self.a(r, i), branch(i, j)))
                # drj => Big OR
                self.add_constraint([neg(d(r, j))] + ands)
                # Big OR => drj
                for andLiteral in ands:
                    self.add_constraint([neg(andLiteral), d(r, j)])
            self.add_constraint([neg(d(r, 1))])

        for j in range(2, n + 1):
            for i in range(int(j/2), j):
                childrens = children(i, n)
                # lij/rij that don't exist are false
                if j not in childrens:
                    self.add_constraint([neg(branch(i, j))])

    def encode_decision(self, k, n):
        '''This will encode the decision (constraints 7 to 13)'''
        # Constraint 7:
        self.discriminateFeature(self.d0, self.r, rr, k, n)

        # Constraint 8:
        self.discriminateFeature(self.d1, self.l, lr, k, n)

        # Constrain 9:
        ands = dict()
        for j in range(1, n + 1):
            for r in range(1, k + 1):
                for i in range(int(j/2), j):
                    if self.u(r, i) + self.p(j,i) not in ands:
                        ands[self.u(r, i) + self.p(j,i)] = self.mk_and(self.u(r,i), self.p(j,i)) 
                    # 1st part: 
                    self.add_constraint([neg(self.u(r,i)), neg(self.p(j,i)), neg(self.a(r,j))])

                # 2nd part
                self.add_constraint([neg(self.u(r,j)), self.a(r, j)] + [ands[self.u(r, i) + self.p(j,i)] for i in range(int(j/2), j)])                
                self.add_constraint([neg(self.a(r,j)), self.u(r,j)])
                for i in range(int(j/2), j):
                    self.add_constraint([neg(ands[self.u(r, i) + self.p(j,i)]), self.u(r,j)])

        # Constraint 10 and 11:
        # For (10) we don't need to do the nodes n and n-1, they are leaves
        # For (11) we don't need to do the node 1, as is the root and non-leaf
        for j in range(1, n + 1):
            literals = [self.a(r, j) for r in range(1, k+1)]
            # Constraint 10
            if j < n - 1:
                self.add_cardinality_constraint(literals)
                self.add_constraint([self.v(j)] + literals)
            # Constraint 11
            if j != 1:
                for r in range(1, k+1):
                    self.add_constraint([neg(self.v(j)), neg(self.a(r, j))])

        # Constraints 12 and 13: j can start in 2 as 1 is root (non-leaf)
        for j in range(2, n+1):
            for q in range(1, len(self.samples) + 1):
                discriminatedSamples = [self.d(self.sigma(r, q), r, j) for r in range(1, k+1)]
                assert(self.eq(q) in (0, 1))
                # Constraint 13
                if self.eq(q) == 0:
                    self.add_constraint([neg(self.v(j)), neg(self.c(j))] + discriminatedSamples)
                # Constraint 12
                if self.eq(q) == 1:
                    self.add_constraint([neg(self.v(j)), self.c(j)] + discriminatedSamples)

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
    debug_solver = False

    print("# reading from stdin")
    nms, samples = parse(sys.stdin)
    print("# encoding")
    e = Enc(nms[0], samples)
    e.enc()
    print("# encoded constraints")
    print("# " + "\n# ".join(map(str, e.constraints)))
    print("# END encoded constraints")
    print("# sending to solver '" + solver + "'")
    cnf = e.mk_cnf(False)
    p = subprocess.Popen(solver, shell=True, stdin=subprocess.PIPE,
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    (output, err) = p.communicate()
    if debug_solver:
        print('\n'.join(lns), file=sys.stderr)
        print(cnf, file=sys.stderr)
    print("# decoding result from solver")
    rc = p.returncode
    lns = str(output, encoding='utf-8').splitlines()
    print(output)
    print(err)
    if len(nms) == 2:
        print("# Expecting {} nodes.".format(nms[1]))
    if rc == 10:
        e.print_model(get_model(lns))
    elif rc == 20:
        print("UNSAT")
    else:
        print("ERROR: something went wrong with the solver")
