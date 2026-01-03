#!/usr/bin/env python3
# -*- coding: utf-8 -*-

# Copyright (C) 2022  Anna Latour
#                     Mate Soos
#
# This program is free software; you can redistribute it and/or
# modify it under the terms of the GNU General Public License
# as published by the Free Software Foundation; version 2
# of the License.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program; if not, write to the Free Software
# Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
# 02110-1301, USA.

import subprocess
import os
import time
import random
import resource
import optparse
import stat
import glob
import re
from collections import namedtuple

maxtimediff = 1
Solver = namedtuple("Solver", "exe dir", defaults=[None, None])


def unique_file(fname_begin, fname_end=".cnf", max_num_files=2700):
    counter = 1
    while True:
        fname = "out/" + fname_begin + '_' + str(counter) + fname_end
        try:
            fd = os.open(
                fname, os.O_CREAT | os.O_EXCL, stat.S_IREAD | stat.S_IWRITE)
            os.fdopen(fd).close()
            return str(fname)
        except OSError:
            pass

        counter += 1
        if counter > max_num_files:
            print("Cannot create unique_file, last try was: %s" % fname)
            exit(-1)

def gen_fuzz_call_brummayer(fuzzer, fname):
    seed = random.randint(0, 1000*1000*1000)
    call = "{0} -s {1} > {2}".format(fuzzer, seed, fname)
    return call

def add_projection(fname) :
    vars = 0
    with open(fname, "r") as f:
        for line in f:
            line = line.strip()
            if len(line) < 3:continue
            if line[0] == "p":
                line = line.split(" ")
                assert line[1].strip() == "cnf"
                vars = int(line[2])

    all_vars = []
    for i in range(vars): all_vars.append(i+1)
    proj = []
    proj_set = {}
    if vars == 0:
        print("ERROR: Can't find 'p cnf' in file %s" % fname)
        exit(-1)

    if random.choice([True, False]):
        num : int = random.randint(int(len(all_vars)/15), int(len(all_vars)/5))
        if random.choice([True, False]):
            num = min(2, len(all_vars))
    else:
        num : int = random.randint(int(len(all_vars)/4), int(len(all_vars)/3))

    num = max(1, num) # at least one variable to project
    for i in range(num):
        proj_set[random.choice(all_vars)] = 1

    for a,_ in proj_set.items():
        proj.append(a)

    with open(fname, "a") as f:
        f.write("c p show ")
        for a in proj:
            f.write("%d " % a)
        f.write("0\n")
    return proj

def set_up_parser():
    usage = "usage: %prog [options] "
    desc = "Fuzz synthesis counter\n"

    parser = optparse.OptionParser(
      usage=usage, description=desc)

    parser.add_option(
      "--verbose", "-v", action="store_true", default=False,
      dest="verbose", help="Print more output")

    parser.add_option(
      "--seed", dest="rnd_seed",
      help="Fuzz test start seed. Otherwise, random seed is picked", type=int)

    parser.add_option(
      "--tout", "-t", dest="maxtime", type=int, default=4,
      help="Max time to run. Default: %default")

    parser.add_option(
      "--only", type=int, dest="only", default=2**40,
      help="Only run N tests. Default: %default")

    return parser


def run(command):
    print("--> Executing: %s" % (" ".join(command)))
    if options.verbose:
        print("CPU limit of parent (pid %d)" % os.getpid(), resource.getrlimit(resource.RLIMIT_CPU))

    p = subprocess.Popen(command, stderr=subprocess.STDOUT,
          stdout=subprocess.PIPE, universal_newlines=True)

    try:
        consoleOutput, err = p.communicate(timeout=options.maxtime)
    except subprocess.TimeoutExpired:
        p.kill()
        consoleOutput, err = p.communicate()
        consoleOutput = "TIMEOUT: Process killed after %d seconds\n" % options.maxtime + consoleOutput

    if options.verbose:
        print("CPU limit of parent (pid %d) after child finished executing" % os.getpid(),
            resource.getrlimit(resource.RLIMIT_CPU))
    return consoleOutput, err


def run_synth(solver, fname):
    curr_time = time.time()
    toexec = solver.split()
    toexec.append(fname)
    out, err = run(toexec)
    if err is None:
        if options.verbose:
            print("No error.")
    else:
        print("Error string is: ", err)
        return True, []
    diff_time = time.time() - curr_time
    if diff_time > options.maxtime - maxtimediff:
        print("Too much time to solve with %s, aborted: " % solver)
        return True, []

    aigs = []
    for line in out.split("\n"):
        line = line.strip()
        # print("Solver output line: %s" % line)
        if ("Training error" not in line) :
            if ("ERROR" in line) or ("Error" in line) or ("error" in line):
                print("Error line from solver %s: %s" % (solver, line))
                return True, []
            if ("assert" in line) or ("Assertion" in line):
                print("Error line from solver %s: %s" % (solver, line))
                return True, []
        if line.startswith("c o Wrote AIG defs:"):
            aigs.append(line[len("c o Wrote AIG defs:"):].strip())

    return False, aigs

def del_core_files():
    items = glob.glob("core-*.cnf")
    for fname in items:
        if os.path.isfile(fname):
            try:
                os.remove(fname)
                print(f"Deleted file: {fname}")
            except OSError as e:
                print(f"Error deleting {fname}: {e}")

def check_core_files():
    # Find all items matching the pattern
    items = glob.glob("core-*.cnf")

    # Filter to ensure NUM is numeric AND it's a regular file
    pattern = re.compile(r'core-(\d+)\.cnf')

    for fname in items:
        # Check if it's a file (not a directory, symlink, etc.)
        if os.path.isfile(fname) and pattern.match(fname):
            out, err = run(["../../cryptominisat", fname])
            if err:
                print(f"ERROR: cannot run cryptominisat on {fname}: {err}")
                exit(-1)
            ok = False
            for line in out.split("\n"):
                line = line.strip()
                if line.startswith("s UNSATISFIABLE"):
                    print(f"Core file {fname} processed successfully with result: {line}")
                    ok = True
                    break
            if not ok:
                print(f"ERROR: core file {fname} did not yield UNSATISFIABLE result")
                exit(-1)
            try:
                os.remove(fname)
                print(f"Deleted file: {fname}")
            except OSError as e:
                print(f"Error deleting {fname}: {e}")
        elif not os.path.isfile(fname) and pattern.match(fname):
            print(f"Skipping non-file item: {fname} (is directory or special file)")
        else:
            print(f"Skipping non-matching item: {fname}")



def gen_fuzz(seed) :
    fname = unique_file("fuzzTest")
    print("Seed: ", seed,  " checking fname: ", fname)
    call = gen_fuzz_call_brummayer("./cnf-fuzz-brummayer.py", fname)
    print("Calling: ", call)
    status = subprocess.call(call, shell=True)
    if status != 0:
        print("Failed fuzzer file generator call: ", call)
        exit(-1)
    else:
        print("Generated fuzz file %s with call: %s" % (fname, call));
    return fname

if __name__ == "__main__":
    if os.path.exists("out") and  os.path.isfile("out"):
        print("ERROR: file 'out' exists, but we need a directory named 'out'")
        exit(-1)

    os.makedirs("out", exist_ok=True)

    # parse options
    parser = set_up_parser()
    (options, args) = parser.parse_args()

    if options.rnd_seed is None:
        b = os.urandom(8)
        rnd_seed = int.from_bytes(b)
        print("Using seed:", rnd_seed)
    else:
        rnd_seed = options.rnd_seed
    random.seed(rnd_seed)

    for i in range(options.only):
        if options.rnd_seed is None:
            b = os.urandom(8)
            seed = int.from_bytes(b)
            random.seed(seed)
        else:
            seed = options.rnd_seed

        del_core_files()

        fname = gen_fuzz(seed)
        add_projection(fname)
        # solver = "./arjun --synth --debugsynth --verb 1"
        solver = "./arjun --verb 2 --synth --synthbve 1 --extend 1 --minimize 0 --debugsynth --samples 10000"
        err, aigs = run_synth(solver, fname)
        if err:
            print("Synthesis failed on file %s" % fname)
            exit(-1)
        print("Synthesis succeeded on file %s, produced files: %s" % (fname, str(aigs)))
        if len(aigs) == 0:
            print("ERROR: Synthesis produced no output AIGs on file %s" % fname)
            exit(-1)
        check_core_files()

        for aig in aigs:
            call = "./test-synth -v -s %d %s %s" % (seed, fname, aig)
            print("Running check command: ", call)
            status = subprocess.call(call, shell=True)
            if status != 0:
                print("Failed fuzzer file generator call: ", call)
                exit(-1)
            print("Call for fuzz OK: %s" % (call));
            os.unlink(aig)
        os.unlink(fname)

    exit(0)
