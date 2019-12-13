#!/usr/bin/env python3
import sys
import subprocess
import time
import re
from id3 import run_id3, get_number_nodes, get_model_id3


solvers = {
    "clingo": ['clingo', '-n1'],
}
solver = solvers["clingo"]
dbg = True

def v(i): return 'v({})'.format(i)
def l(i, j): return 'l({},{})'.format(i, j)
def r(i, j): return 'r({},{})'.format(i, j)
def p(j, i): return 'p({},{})'.format(j, i)
def a(r, i): return 'a({},{})'.format(r, i)
def c(i): return 'c({})'.format(i)
def d(sigma, r, j): return 'd{}({},{})'.format(sigma, r, j)

def eq(samples, q):
    '''Returns the classification of example q'''
    assert(q > 0 and q <= len(samples))
    return samples[q-1][-1]

def sigma(samples, r, q):
    '''Returns fr value for example q'''
    assert(q > 0 and q <= len(samples))
    return samples[q-1][r-1]

def encode_samples(k,samples):
    res = ""
    q = len(samples)
    for q in range(1, len(samples) + 1):
        res += "1{"
        for r in range(1,k+1):
            res +=  d(sigma(samples,r,q),r,"J") + ";"
        res = res[:-1]
        res += "} :- v(J),"
        if eq(samples,q) == 0:
            res += "c(J).\n"
        else:
            res += "not c(J).\n"
    return res

def print_model(model, node_count):
    '''prints SAT model'''
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
    for i in range(2, node_count + 1):
        if v(i) in model and model[v(i)]:
            leaves.append(i)

    for i in leaves:
        if c(i) not in model:
            print("c {} {}".format(i, 0))
        else:
            print("c {} {}".format(i, {False: 0, True: 1}[model[c(i)]]))

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

    classifications = []
    for i in range(len(samples)):
        classifications.append(samples[i][-1])

    featuresClassification = []
    for sample in samples:
        featuresClassification.extend(sample[:-1])
    return (nms, samples, featuresClassification, classifications)


def read_model(modlines):
    def get_atom_params(a): return a[a.find('(') + 1: a.find(')')].split(',')
    def get_int_atom_params(a): return map(int, get_atom_params(a))

    has_answer = False
    model = {}
    for l in modlines:
        l = l.strip()
        if not l:
            continue
        if has_answer:  # parse answer set
            els = l.split()
            for e in els:
                if e.startswith('v('):
                    model['v({})'.format(*get_int_atom_params(e))] = True
                if e.startswith('c('):
                    model['c({})'.format(*get_int_atom_params(e))] = True
                if e.startswith('l('):
                    model['l({},{})'.format(*get_int_atom_params(e))] = True
                if e.startswith('r('):
                    model['r({},{})'.format(*get_int_atom_params(e))] = True
                if e.startswith('a('):
                    model['a({},{})'.format(*get_int_atom_params(e))] = True
            break
        elif l.startswith('Answer'):
            has_answer = True
    return model if has_answer else None


def enconde_run_asp(n, k, samples, featuresClassification, classifications):
    global solver, dbg
    sol_in = '#const n = {}.\n'.format(n)
    sol_in += '#const k = {}.\n'.format(k)
    with open('main.lp') as mf:
        sol_in += '\n' + mf.read()

    sol_in += encode_samples(k,samples)
    if dbg:
        sys.stderr.write(sol_in)
    sys.stdout.write('# running {}\n'.format(solver))
    t0 = time.time()
    p = subprocess.Popen(solver, stdin=subprocess.PIPE,
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    (po, pe) = p.communicate(input=bytes(sol_in, encoding='utf-8'))
    po = str(po, encoding='utf-8').splitlines()
    pe = str(pe, encoding='utf-8').splitlines()
    sys.stdout.write('# solver ended with exit code {} ({:.2f} s)\n'.format(
        p.returncode, time.time() - t0))
    if p.returncode % 10 != 0:
        sys.stderr.write('something went wrong with the call to {} (exit code {})'.format(
            solver, p.returncode))
        sys.stderr.write('\n>>' + '\n>>'.join(po) + '\n')
        sys.stderr.write('\nerr>>' + '\nerr>>'.join(pe) + '\n')
        exit(1)
    if dbg:
        sys.stderr.write('\n>>' + '\n>>'.join(po) + '\n')
        sys.stderr.write('\nerr>>' + '\nerr>>'.join(pe) + '\n')
    return None if p.returncode == 20 else read_model(po)


if __name__ == "__main__":
    print("# reading from stdin")
    nms, samples, featuresClassification, classifications = parse(sys.stdin)
    print("# Running id3")
    root = run_id3(samples, nms[0])
    n = get_number_nodes(root)
    model = get_model_id3(root)
    if n % 2 == 0:
        # Returns an even number of nodes (it shouldn't happen, just for precaution)
        n += 1
        model = enconde_run_asp(n, nms[0], samples, featuresClassification, classifications)
    elif model == None:
        model = enconde_run_asp(n, nms[0], samples, featuresClassification, classifications)

    print("# Obtained tree with {} nodes from id3".format(n))
    i = n - 2
    node_count = n
    while True:
        if node_count == 1:
            i = 3
        if i < 3:
            break
        new_model = enconde_run_asp(i, nms[0], samples, featuresClassification, classifications)
        if new_model == None:  # => UNSAT
            print("# UNSAT {} nodes, output last SAT model".format(i))
            break
        else:
            print("# SAT {} nodes".format(i))
            node_count = i
            i -= 2
            model = new_model

    print_model(model, node_count)
    print("# Model has {} nodes".format(node_count))

    #new_model = enconde_run_smt(
    #    nms[1], nms[0], samples, featuresClassification, classifications)
    #print_model(new_model, nms[1])
    if len(nms) == 2:
        print("# Expecting {} nodes.".format(nms[1]))
