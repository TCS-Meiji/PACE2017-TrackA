#!/usr/bin/env python3

'''
Automatically test a given treewidth solver:
    ./autotest-tw-solver.py path/to/my/solver

The test is run on some corner cases, and on graphs were past PACE submissions
exhibited bugs.

Optional argument:
    --full   run test on all graphs with min-degree 3 and at most 8 vertices

Requires python3-networkx

Copyright 2016, Holger Dell
Licensed under GPLv3.
'''

import os
import subprocess
import threading
import glob
import tempfile
import signal
import argparse
import networkx



def read_tw_from_td(ifstream):
    '''Return the reported treewidth from a .td file'''
    for line in ifstream:
        if line[0] == 's':
            treewidth=int(line.split(' ')[3]) - 1
            return treewidth


def test_case_generator(full=False):
    '''
    Return a generator for all test cases.
    
    Each test case is a tuple (name, grfilestream, treewidth)
    where
      - name is a string indicating the name of the test case
      - grfilestream is a stream from which the grfile can be read
      - treewidth is the known treewidth of the graph (or None if we don't care)
    '''

    # This covers some corner cases (comments, empty graphs, etc)
    for grfile in glob.glob('test/valid/*.gr'):
        yield grfile,open(grfile,'r'),None

    # Test cases where some tw-solvers were buggy in the past
    for grfile in glob.glob('test/tw-solver-bugs/*.gr'):
        treewidth = None
        with open(grfile[:-3] + '.td') as td_stream:
            treewidth = read_tw_from_td(td_stream)
        yield grfile,open(grfile,'r'),treewidth

    # More test cases where some tw-solvers were buggy in the past
    tests=[ 'test/tw-solver-bugs.graph6' ]

    if full:
        tests.append('test/n_upto_8.graph6')
 
    for fname in tests:
        with open(fname) as tests:
            for line in tests:
                line = line.strip().split(' ')
                graph6 = line[0]
                treewidth = int(line[1])

                G = networkx.parse_graph6(graph6)
                n = G.order()
                m = G.size()

                with tempfile.TemporaryFile('w+') as tmp:
                    tmp.write("p tw {:d} {:d}\n".format(n,m))
                    for (u,v) in G.edges(data=False):
                        tmp.write("{:d} {:d}\n".format(u+1,v+1))
                    tmp.flush()
                    tmp.seek(0)
                    yield graph6 + ' from ' + fname,tmp,treewidth


tw_executable = ''
FNULL = open(os.devnull, 'w')

def td_validate(grstream, tdstream):
    with tempfile.NamedTemporaryFile('w+') as tmp_td:
        for line in tdstream:
            tmp_td.write(line)
        tmp_td.flush()
        tmp_td.seek(0)
        with tempfile.NamedTemporaryFile('w+') as tmp_gr:
            for line in grstream:
                tmp_gr.write(line)
            tmp_gr.flush()
            tmp_gr.seek(0)

            p = subprocess.Popen(['./td-validate',tmp_gr.name,tmp_td.name])
            p.wait()
            return p.returncode == 0
 

def run_one_testcase(arg):
    '''given the name of a testcase, the input stream for a .gr file, and the
    correct treewidth, this function runs the test'''
    
    global tw_executable
    name, ifstream, treewidth = arg
 
    with tempfile.TemporaryFile('w+') as tmp_td:
        p = subprocess.Popen([tw_executable],
                stdin=ifstream,
                stdout=tmp_td,
                stderr=FNULL)
    
        try:
            p.wait(timeout=5)
        except subprocess.TimeoutExpired:
            p.terminate()
            try:
                p.wait(timeout=5)
            except subprocess.TimeoutExpired:
                p.kill()

        ifstream.seek(0)
        tmp_td.flush()
        tmp_td.seek(0)
        print(name)
        valid = td_validate(ifstream, tmp_td)
        ifstream.close()

        tmp_td.seek(0)
        computed_tw = read_tw_from_td(tmp_td)

        if treewidth != None and computed_tw != None:
            if treewidth > computed_tw:
                print('!! your program said tw={:d} but we thought it was {:d} -- please send your .td file to the developer of td-validate'.format(computed_tw,treewidth))
            elif treewidth < computed_tw:
                print("non-optimal (your_tw={:d}, optimal_tw={:d})".format(computed_tw,treewidth))
        nonoptimal = treewidth != None and computed_tw != None and treewidth < computed_tw
        print()
        return valid,nonoptimal

def main():
    parser = argparse.ArgumentParser(description='Automatically test a given treewidth solver')
    parser.add_argument("twsolver", help="path to the treewidth solver you want to test")
    parser.add_argument("--full", help="run test on all 2753 graphs with min-degree 3 and at most 8 vertices (this could take a while)",
            action='store_true')

    args = parser.parse_args()

    global tw_executable
    tw_executable = args.twsolver

    f='./td-validate'
    if not os.path.isfile(f):
        print("File {:s} not found. Run 'make' first!\n".format(f))
        return

    print("Automatically testing {:s}...\n".format(tw_executable))

    results = list(map(run_one_testcase, test_case_generator(args.full)))

    total=len(results)
    total_valid = 0
    total_nonoptimal = 0
    for valid,nonoptimal in results:
        if valid: total_valid += 1
        if nonoptimal: total_nonoptimal += 1

    print()
    if total == total_valid:
        print('Produced a valid .td on all {:d} instances.'.format(total))
    else:
        print('{:d} out of {:d} tests produced a valid .td'.format(total_valid,total))
    if total_nonoptimal == 0:
        print('All tree decompositions were optimal')
    else:
        print('{:d} tree decompositions were not optimal'.format(total_nonoptimal))

if __name__ == '__main__':
    main()
