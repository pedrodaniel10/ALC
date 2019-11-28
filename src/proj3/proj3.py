#!/usr/bin/env python3
import sys
import subprocess
import re
from id3 import run_id3, get_number_nodes, get_model_id3


unsat_msg = '__UNSAT__'
solvers = {
    "CPLEX": ['minizinc', '--unsat-msg', unsat_msg,  '--solver', 'CPLEX',
              '--cplex-dll', '/opt/ibm/ILOG/CPLEX_Studio129/opl/bin/x86-64_linux/libcplex1290.so', '-'],
    "Chuffed": ['minizinc', '--unsat-msg', unsat_msg,  '--solver', 'Chuffed', '-'],
    "Geocode": ['minizinc', '--unsat-msg', unsat_msg,  '-']
}
solver = solvers["Chuffed"]


def v(i): return 'v[{}]'.format(i)
def l(i, j): return 'l[{},{}]'.format(i, j)
def r(i, j): return 'r[{},{}]'.format(i, j)
def p(j, i): return 'p[{},{}]'.format(j, i)
def a(r, i): return 'a[{},{}]'.format(r, i)
def c(i): return 'c[{}]'.format(i)

def print_model(model):
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


def enconde_run_smt(n, k, samples, featuresClassification, classifications):
    global solver
    print("# encoding with {} nodes".format(n))

    dbg = False  # set to True if you want to see what goes into minizinc
    sol_in = ''
    sol_in += 'int: n = {};\n'.format(n)
    sol_in += 'int: k = {};\n'.format(k)
    sol_in += 'int: qlen = {};\n'.format(len(classifications))
    # add main.mzn to the input
    with open('main.mzn') as mf:
        sol_in += '\n' + mf.read()
    # add samples
    sol_in += "constraint samples = array2d(QLEN,FEATURES,{});\n".format(featuresClassification)
    sol_in += "constraint eq ={};\n".format(classifications)
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
    nms, samples, featuresClassification, classifications = parse(sys.stdin)
    print("# Running id3")
    root = run_id3(samples, nms[0])
    n = get_number_nodes(root)
    model = get_model_id3(root)
    if n % 2 == 0:
        # Returns an even number of nodes (it shouldn't happen, just for precaution)
        n += 1
        model = enconde_run_smt(n, nms[0], samples, featuresClassification, classifications)
    elif model == None:
        model = enconde_run_smt(n, nms[0], samples, featuresClassification, classifications)

    print("# Obtained tree with {} nodes from id3".format(n))
    i = n - 2
    node_count = n
    while True:
        if node_count == 1:
            i = 3
        if i < 3:
            break
        new_model = enconde_run_smt(i, nms[0], samples, featuresClassification, classifications)
        if new_model == None:  # => UNSAT
            print("# UNSAT {} nodes, output last SAT model".format(i))
            break
        else:
            print("# SAT {} nodes".format(i))
            node_count = i
            i -= 2
            model = new_model

    print_model(model)
    print("# Model has {} nodes".format(node_count))

    if len(nms) == 2:
        print("# Expecting {} nodes.".format(nms[1]))
