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

    # if we want bigger CNFs
    # call = "{0} -s {1} -i 14 -I 30 > {2}".format(fuzzer, seed, fname)

    # if we want smaller CNFs
    # call = "{0} -s {1} -i 2 -I 4 > {2}".format(fuzzer, seed, fname)
    return call

def add_projection(fname) :
    vars = 0
    with open(fname, "r") as f:
        for line in f:
            line = line.strip()
            if len(line) < 3:
                continue
            if line[0] == "p":
                line = line.split(" ")
                assert line[1].strip() == "cnf"
                vars = int(line[2])

    all_vars = []
    for i in range(vars):
        all_vars.append(i+1)
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
      "--tout", "-t", dest="maxtime", type=int, default=12,
      help="Max time to run. Default: %default")

    parser.add_option(
      "--num", "-n", dest="num", type=int, default=None,
      help="Number of fuzz iterations to run. Default: unlimited")

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
    return consoleOutput, err, p.returncode

def run_check(command, final):
    ok = False

    p = subprocess.Popen(command, stderr=subprocess.STDOUT,
          stdout=subprocess.PIPE, universal_newlines=True)
    try:
        consoleOutput, err = p.communicate()
    except:
        p.kill()
        print("ERROR: check process failed")
        exit(-1)

    if err is not None:
        print("Error string is: ", err)
        exit(-1)

    for line in consoleOutput.split("\n"):
        if "CORRECT" in line:
            print("Check output: %s" % line)
            ok = True

    if not ok and final:
        print("ERROR: check process did not report CORRECT")
        exit(-1)


def run_synth(solver, fname):
    curr_time = time.time()
    toexec = solver.split()
    toexec.append(fname)
    out, err, returncode = run(toexec)
    if err is None:
        if options.verbose:
            print("No error.")
    else:
        print("Error string is: ", err)
        return True, []
    diff_time = time.time() - curr_time
    if diff_time > options.maxtime - maxtimediff:
        print("Too much time to solve with %s, aborted: " % solver)
        return None, []
    if returncode != 0 and not out.startswith("TIMEOUT"):
        print("Solver crashed with exit code %d (signal %d)" % (returncode, -returncode))
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
            out, err, _ = run(["../../cryptominisat", fname])
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

def is_unsat(fname) :
    unsat_check = "../../cryptominisat/build/cryptominisat5"
    curr_time = time.time()
    toexec = unsat_check.split()
    toexec.append(fname)
    out, err, _ = run(toexec)
    if err is None:
        if options.verbose:
            print("No error.")
    else:
        print("Error string is: ", err)
        return True
    diff_time = time.time() - curr_time
    if diff_time > options.maxtime - maxtimediff:
        print("Too much time to solve with %s, aborted: " % unsat_check)
        return True

    for line in out.split("\n"):
        line = line.strip()
        if line.startswith("s UNSATISFIABLE"):
            print("File %s is UNSAT" % fname)
            return True
        if line.startswith("s SATISFIABLE"):
            print("File %s is SAT" % fname)
            return False

    print("ERROR: Could not determine if file %s is SAT or UNSAT" % fname)
    exit(-1)

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
        print("Generated fuzz file %s with call: %s" % (fname, call))
    return fname

def cleanup(fname, prefix):
    os.unlink(fname)
    directory = "."
    for file_path in glob.glob(os.path.join(directory, f"{prefix}*.aig")):
        if os.path.isfile(file_path):
            os.remove(file_path)
            print(f"Deleted: {os.path.basename(file_path)}")
    os.unlink(prefix)

def gen_mstrategy():
    # Valid types: "const" and "bve". ("learn" requires EXTRA_SYNTH, so skip it.)
    types = ["const", "bve"]

    uint_params = ["samples", "samples_ccnr", "max_depth", "sampler_fixed_conflicts",
                   "min_leaf_size", "simplify_every",
                   "bias_samples", "const_vote_samples", "stats_every",
                   "detailed_stats_every", "rebuild_min_loops", "rebuild_min_clauses",
                   "rebuild_growth_num", "rebuild_growth_den",
                   "reduce_cex_gen_ok", "reduce_cex_tot_rep", "reduce_cex_need_rep",
                   "reduce_cex_cz_min_rep",
                   "simplify_repair_every", "skip_input_only_min_rep", "skip_input_only_ratio",
                   "conflict_drop_y_max", "extra_minim_hot", "extra_minim_very_hot",
                   "conflict_cap", "conflict_cap_keep", "batch_minim_min",
                   "minim_budget_threshold", "minim_budget_max", "minim_budget_mult",
                   "aig_simplify_every", "td_steps", "td_lookahead_iters",
                   "better_ctx_remove_all",
                   "td_max_edges", "ccnr_mems_per_sample", "ccnr_per_call_limit",
                   "reduce_cex_gen_ratio_num", "reduce_cex_gen_ratio_den",
                   "cz_high_ratio", "cz_low_ratio",
                   "cz_threshold_high", "cz_threshold_mid", "cz_threshold_low"]
    int_params  = ["filter_samples", "biased_sampling", "minimize_conflict",
                   # maxsat_better_ctx=1 requires EXTRA_SYNTH — omit from strategies
                   "maxsat_order", "use_all_vars_as_feats",
                   "repair_cache_size", "backward_synth_order", "manthan_order",
                   "manthan_on_the_fly_order", "one_repair_per_loop", "force_bw_equal",
                   "bva_xor_vars", "silent_var_update", "inv_learnt", "do_td_contract"]
    #  "ctx_solver_type", "repair_solver_type",
    double_params = ["min_gain_split", "bias_w_high", "bias_p_low", "bias_p_high"]

    def gen_uint():
        return str(random.choice([0, 1, 10, 100, 400, 1000]))

    def gen_int():
        return str(random.choice([0, 1, 2]))

    def gen_double():
        return str(random.choice([0.0, 0.001, 0.1, 0.35, 0.5, 0.65, 0.9, 1.0]))

    def gen_strategy(must_have_max_repairs, must_not_have_max_repairs=False):
        stype = random.choice(types)
        params = {}
        if must_have_max_repairs or (not must_not_have_max_repairs and random.choice([True, False])):
            params["max_repairs"] = str(random.choice([10, 100, 400, 1000]))
        for p in random.sample(uint_params, random.randint(0, 2)):
            params.setdefault(p, gen_uint())
        for p in random.sample(int_params, random.randint(0, 2)):
            params.setdefault(p, gen_int())
        for p in random.sample(double_params, random.randint(0, 1)):
            params.setdefault(p, gen_double())
        if not params:
            return stype
        param_str = ",".join("%s=%s" % (k, v) for k, v in params.items())
        return "%s(%s)" % (stype, param_str)

    n = random.randint(1, 3)
    strategies = []
    for i in range(n):
        strategies.append(gen_strategy(must_have_max_repairs=(i < n - 1),
                                       must_not_have_max_repairs=(i == n - 1)))
    return ",".join(strategies)


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

    i = 0
    while options.num is None or i < options.num:
        i += 1
        if options.rnd_seed is None:
            b = os.urandom(8)
            seed = int.from_bytes(b)
            random.seed(seed)
        else:
            seed = options.rnd_seed

        del_core_files()

        fname = gen_fuzz(seed)
        add_projection(fname)
        if is_unsat(fname):
            print("Generated file %s is UNSAT, skipping synthesis" % fname)
            os.unlink(fname)
            continue
        # solver = "./arjun --synth --debugsynth --verb 1"
        prefix = unique_file("fuzzTest")
        print("Using prefix %s for synthesis output files" % prefix)
        solver = "./arjun --verb 2 --debugsynth %s " % prefix
        if random.choice([True, False]):
            solver += "--synth "
        else:
            solver += "--synthmore "

        opts = [
            " --synthbve"
            , " --extend"
            , " --minimize"
            , " --minimconfl"
            , " --filtersamples"
            , " --biasedsampling"
            , " --uniqsamp"
            , " --unate"
            , " --ctxsolver"
            , " --repairsolver"
            , " --unatedef"
            , " --bwequal"
            , " --bvaxor"
            , " --silentupdate"
            , " --learnuseall"
            , " --monflyorder"
        ]
        for o in opts:
            val = random.choice([0, 1])
            solver += o + " " + str(val)

        # Pure boolean flag (no 0/1 value). ~1-in-2 coverage.
        if random.choice([True, False]):
            solver += " --sat-sweep"

        solver += " --morder " + str(random.randint(0, 2))
        solver += " --bveresolvmaxsz " + str(random.randint(2, 20))
        solver += " --iter1grow " + str(random.randint(0, 5))
        solver += " --iter2grow " + str(random.choice([0, 10, 100]))
        solver += " --samplesccnr " + random.choice(["0", "100", "10000"])
        solver += " --samples " + random.choice(["0", "100", "10000"])
        solver += " --mingainsplit " + random.choice(["0.1", "0.001", "5"])
        solver += " --simpevery " + random.choice(["1", "100", "10000"])
        solver += " --maxdepth " + random.choice(["2", "10"])
        solver += " --minleaf " + random.choice(["2", "10"])
        solver += " --maxsat " + random.choice(["0", "-1"])  # skip 1 (requires EXTRA_SYNTH)
        solver += " --repaircache " + " " + random.choice(["0", "100", "1000"])

        # Hard-coded cutoff constants (very low and very high values)
        solver += " --biassamples " + random.choice(["0", "1", "5", "50", "500", "5000"])
        solver += " --constvotesamples " + random.choice(["0", "1", "2", "10", "100"])
        solver += " --statsevery " + random.choice(["0", "1", "10", "40", "1000"])
        solver += " --detailedstatsevery " + random.choice(["0", "1", "10", "200", "5000"])
        solver += " --rebuildminloops " + random.choice(["1", "5", "50", "200", "10000"])
        solver += " --rebuildminclauses " + random.choice(["1", "100", "1000", "100000", "1000000"])
        solver += " --rebuildgrownum " + random.choice(["0.02", "0.1", "1", "2", "10"])
        solver += " --rebuildgrowden " + random.choice(["0", "0.5", "1", "3", "10"])
        solver += " --reducecexgenok " + random.choice(["1", "5", "20", "100", "10000"])
        solver += " --reducecextotrep " + random.choice(["1", "10", "100", "2000", "100000"])
        solver += " --reducecexneedrep " + random.choice(["0", "1", "3", "10", "1000"])
        solver += " --reducecexczminrep " + random.choice(["1", "10", "100", "10000"])
        solver += " --simprepevery " + random.choice(["0", "1", "10", "1000", "100000"])
        solver += " --skipinputminrep " + random.choice(["1", "10", "200", "10000"])
        solver += " --skipinputratio " + random.choice(["1", "5", "20", "100"])
        solver += " --confldropy " + random.choice(["1", "5", "25", "100", "10000"])
        solver += " --extraminimhot " + random.choice(["1", "5", "10", "100", "10000"])
        solver += " --extraminimvhot " + random.choice(["1", "10", "30", "100", "10000"])
        solver += " --conflcap " + random.choice(["1", "5", "10", "40", "200", "100000"])
        solver += " --conflcapkeep " + random.choice(["1", "2", "5", "30", "100", "100000"])
        solver += " --batchminimmin " + random.choice(["1", "3", "6", "20", "10000"])
        solver += " --minimbudgetthresh " + random.choice(["1", "5", "20", "100", "10000"])
        solver += " --minimbudgetmax " + random.choice(["1", "10", "150", "1000", "100000"])
        solver += " --minimbudgetmult " + random.choice(["1", "2", "4", "10", "100"])
        solver += " --aigsimpevery " + random.choice(["0", "1", "5", "50", "10000"])
        solver += " --tdsteps " + random.choice(["100", "1000", "100000", "1000000"])
        solver += " --tdlookahead " + random.choice(["1", "10", "300", "1000"])
        solver += " --bctxremoveall " + random.choice(["1", "3", "5", "20", "10000"])
        solver += " --tdcontract " + random.choice(["0", "1"])
        solver += " --tdmaxedges " + random.choice(["1", "10", "100", "1000", "70000", "10000000"])
        solver += " --ccnrmemspersample " + random.choice(["0", "1", "100", "1000", "100000", "10000000"])
        solver += " --ccnrpercalllimit " + random.choice(["0", "1", "100", "1000", "50000", "10000000"])
        solver += " --biaswgh " + random.choice(["0.0", "0.1", "0.5", "0.9", "1.0"])
        solver += " --biasplow " + random.choice(["0.0", "0.1", "0.35", "0.5"])
        solver += " --biasphigh " + random.choice(["0.5", "0.65", "0.9", "1.0"])
        solver += " --reducecexgenrationum " + random.choice(["0", "1", "3", "10", "1000"])
        solver += " --reducecexgenratioden " + random.choice(["1", "2", "4", "10", "1000"])
        solver += " --czhighratio " + random.choice(["0", "1", "3", "10", "1000"])
        solver += " --czlowratio " + random.choice(["0", "1", "2", "5", "100"])
        solver += " --czthreshhigh " + random.choice(["0", "1", "2", "5", "1000"])
        solver += " --czthreshmid " + random.choice(["0", "1", "2", "5", "1000"])
        solver += " --czthreshlow " + random.choice(["0", "1", "2", "5", "1000"])

        solver += " --mstrategy " + gen_mstrategy()

        err, aigs = run_synth(solver, fname)
        if err is None:
            print("Synthesis timed out on file %s" % fname)
            cleanup(fname, prefix)
            continue
        if err:
            print("Synthesis failed on file %s" % fname)
            print("=" * 60)
            print("REPRODUCE with: python3 ../scripts/fuzz_synth.py --seed %d --num 1" % seed)
            print("=" * 60)
            exit(-1)
        print("Synthesis succeeded on file %s, produced files: %s" % (fname, str(aigs)))
        if len(aigs) == 0:
            print("ERROR: Synthesis produced no output AIGs on file %s" % fname)
            exit(-1)
        check_core_files()

        for aig in aigs:
            final = "final" in aig
            if final:
                call = "./test-synth -u -v -s %d %s %s" % (seed, fname, aig)
            else:
                call = "./test-synth -v -s %d %s %s" % (seed, fname, aig)
            print("Running check command: ", call)
            run_check(call.split(), final)
            os.unlink(aig)
        cleanup(fname, prefix)
    exit(0)
