#!/usr/bin/env python3
# -*- coding: utf-8 -*-
#
# Focused fuzzer for synthesis_unate_def_rep. Forces --unatedef 1 and
# --unatedefrep 1 on every run, and explicitly verifies the
# *-unsat_unate_def_rep.aig output AIG against the original CNF using
# test-synth. The general fuzz_synth.py randomizes these flags so the
# rep pass only fires sometimes; this script exists to drive it on every
# input and to fail fast on incorrect AIGs from this specific stage.

import glob
import os
import random
import re
import stat
import subprocess
import sys


MAX_TIME = 60


def unique_file(prefix, suffix=".cnf", max_num=10000):
    counter = 1
    while True:
        fname = "out/" + prefix + '_' + str(counter) + suffix
        try:
            fd = os.open(fname, os.O_CREAT | os.O_EXCL,
                         stat.S_IREAD | stat.S_IWRITE)
            os.fdopen(fd).close()
            return fname
        except OSError:
            pass
        counter += 1
        if counter > max_num:
            print("ERROR: cannot create unique_file, last try: %s" % fname)
            sys.exit(1)


def gen_cnf(seed):
    fname = unique_file("rep_in")
    cmd = "./cnf-fuzz-brummayer.py -s %d > %s" % (seed, fname)
    rc = subprocess.call(cmd, shell=True)
    if rc != 0:
        print("ERROR: brummayer failed seed=%d" % seed)
        sys.exit(1)
    add_projection(fname)
    return fname


def add_projection(fname):
    nvars = 0
    with open(fname, 'r') as f:
        for line in f:
            line = line.strip()
            if line.startswith('p '):
                parts = line.split()
                nvars = int(parts[2])
                break
    if nvars == 0:
        sys.exit(1)
    # ~1/3 to 1/2 of vars projected — enough for the rep pass to have work.
    n = max(1, random.randint(nvars // 4, nvars // 2 + 1))
    proj = random.sample(range(1, nvars + 1), n)
    with open(fname, 'a') as f:
        f.write("c p show " + " ".join(str(v) for v in proj) + " 0\n")


def is_sat(fname):
    cms = "../../cryptominisat/build/cryptominisat5"
    if not os.path.exists(cms):
        # fallback: pretend SAT
        return True
    try:
        out = subprocess.run([cms, fname], capture_output=True, text=True,
                             timeout=10)
    except subprocess.TimeoutExpired:
        return False
    for line in out.stdout.splitlines():
        if line.startswith('s SATISFIABLE'):
            return True
        if line.startswith('s UNSATISFIABLE'):
            return False
    return False


def run_arjun(fname, prefix):
    """Run arjun with the rep pass forced on. Randomize knobs that matter
    for the rep pass while keeping the rest of the pipeline standard."""
    args = [
        "./arjun", "--synth", "--debugsynth", prefix,
        "--verb", "1",
        "--unatedef", "1",
        "--unatedefrep", "1",
        # 0 = inner loop never runs (no commits); high values stress refinement.
        "--unatedefrepiters", str(random.choice([0, 1, 5, 30, 100, 10000])),
        # 0 = skip every CEX (no refinement); 1000 = effectively unlimited.
        "--unatedefrepmaxpat", str(random.choice([0, 1, 4, 12, 50, 1000])),
        # 0 = give up on first cost-zero; high = never give up.
        "--unatedefrepmaxcz", str(random.choice([0, 1, 2, 5, 30])),
        # 1 = mostly time out; 100000 = never.
        "--unatedefrepconfl", str(random.choice([1, 10, 100, 1000, 100000])),
        # 0=input only, 1=+backward-defined, 2=+to-define (richest).
        "--unatedefrepaux", str(random.choice([0, 1, 2])),
        # 0 = no conflict minim (old). 1 = greedy. Mostly we want 1.
        "--unatedefrepminim", str(random.choice([0, 1])),
        # 0 = budget burnt instantly (no minim work even if enabled). High
        # values let minim grind through patterns. Stress both extremes.
        "--unatedefrepminbud", str(random.choice([0, 1, 4, 16, 200])),
        # 0=off; 1=always; 2=only when aux non-empty.
        "--unatedefrepinpfirst", str(random.choice([0, 1, 2])),
        # 0/1: single-shot drop-all-aux after greedy minim.
        "--unatedefrepdropaux", str(random.choice([0, 1])),
        # 1 = single CEX (off), 2..8 = collect that many.
        "--unatedefrepmulticex", str(random.choice([1, 2, 3, 5, 8])),
        # iter-trace verbosity threshold. Sometimes set low so the
        # trace fires (stress-testing the printing code).
        "--unatedefrepiterverb", str(random.choice([0, 1, 4, 99])),
        # 0/1: sort minim drop order by pattern-frequency.
        "--unatedefrepfreqsort", str(random.choice([0, 1])),
        "--unatedefcond", str(random.choice([0, 1])),
        "--unatedefcondmax", str(random.choice([0, 1, 16, 1024])),
        "--unatedefconddry", str(random.choice([1, 10, 100, 100000])),
        # keep manthan strategies tame so most runs finish fast
        "--mstrategy", "const(max_repairs=50),bve",
        fname,
    ]
    try:
        out = subprocess.run(args, capture_output=True, text=True,
                             timeout=MAX_TIME)
    except subprocess.TimeoutExpired:
        return None, [], None
    aigs = []
    saw_rep_done = False
    for line in out.stdout.splitlines():
        if "[unate_def_rep] Done." in line:
            saw_rep_done = True
        if line.startswith("c o Wrote AIG defs:"):
            aigs.append(line[len("c o Wrote AIG defs:"):].strip())
        if "ERROR" in line and "Training error" not in line:
            print("ERROR line: %s" % line)
            return True, aigs, saw_rep_done
        if "Assertion" in line or "assert" in line:
            print("Assertion line: %s" % line)
            return True, aigs, saw_rep_done
    if out.returncode != 0:
        print("arjun crashed exit=%d args=%s" % (out.returncode, " ".join(args)))
        return True, aigs, saw_rep_done
    return False, aigs, saw_rep_done


def run_test_synth(cnf, aig, final):
    args = ["./test-synth", "-v", "1"]
    if final:
        args.append("-u")
    args += [cnf, aig]
    out = subprocess.run(args, capture_output=True, text=True, timeout=30)
    # test-synth uses different success markers for partial vs final AIGs:
    # - final (-u): "AIGs are CORRECT" / "verified CORRECT" via UNSAT miter
    # - partial: "Randomized success" / "all samples satisfied" via N-sample
    #   randomized check. Both kinds of failure print "INCORRECT" or assert.
    for line in out.stdout.splitlines():
        if "INCORRECT" in line:
            print("test-synth INCORRECT on aig=%s" % aig)
            print(out.stdout[-2000:])
            return False
    for line in out.stdout.splitlines():
        if "CORRECT" in line:
            return True
        if "Randomized success" in line:
            return True
        if "all samples satisfied" in line:
            return True
    print("test-synth FAILED on aig=%s cnf=%s (no success marker)" % (aig, cnf))
    print(out.stdout[-2000:])
    return False


def cleanup(fname, prefix):
    for p in [fname]:
        if os.path.isfile(p):
            os.remove(p)
    for f in glob.glob(prefix + "*.aig"):
        if os.path.isfile(f):
            os.remove(f)
    if os.path.isfile(prefix):
        os.remove(prefix)


def main():
    if len(sys.argv) > 1:
        num = int(sys.argv[1])
    else:
        num = 100
    seed_arg = sys.argv[2] if len(sys.argv) > 2 else None
    if seed_arg is not None:
        random.seed(int(seed_arg))

    os.makedirs("out", exist_ok=True)
    rep_fired = 0
    rep_verified = 0
    for i in range(num):
        seed = random.randint(0, 1 << 31)
        random.seed(seed)
        fname = gen_cnf(seed)
        if not is_sat(fname):
            os.remove(fname)
            continue
        prefix = unique_file("rep_out", suffix="")
        err, aigs, saw_rep_done = run_arjun(fname, prefix)
        if err is None:
            print("seed=%d TIMEOUT" % seed)
            cleanup(fname, prefix)
            continue
        if err:
            print("FAIL seed=%d cnf=%s prefix=%s" % (seed, fname, prefix))
            sys.exit(1)
        if saw_rep_done:
            rep_fired += 1
        # Verify each intermediate AIG (incl. unate_def_rep specifically).
        for aig in aigs:
            final = "-final.aig" in aig
            if not run_test_synth(fname, aig, final):
                print("FAIL test-synth seed=%d aig=%s" % (seed, aig))
                sys.exit(1)
            if "unate_def_rep" in aig:
                rep_verified += 1
        cleanup(fname, prefix)
        if (i + 1) % 25 == 0:
            print("[fuzz_unate_def_rep] %d/%d so far rep_fired=%d rep_verified=%d" %
                  (i + 1, num, rep_fired, rep_verified))
    print("DONE %d iters: rep_fired=%d rep_verified_AIGs=%d" %
          (num, rep_fired, rep_verified))


if __name__ == "__main__":
    main()
