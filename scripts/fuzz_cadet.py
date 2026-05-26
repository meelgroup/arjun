#!/usr/bin/env python3
# -*- coding: utf-8 -*-

# Copyright (C) 2026  Mate Soos
#
# This program is free software; you can redistribute it and/or
# modify it under the terms of the GNU General Public License
# as published by the Free Software Foundation; version 2
# of the License.

"""Fuzzer for the in-tree CADET port (`--cadet 1`).

Generates small Brummayer-style CNFs, adds a projection, runs arjun with
`--cadet 1` to synthesize the un-projected vars, and verifies the result
with `test-synth`. Mirrors the structure of `fuzz_synth.py` but trims
the option matrix to flags CADET actually consumes, and clamps the
projection so the number of inputs reaching CADET stays inside what
Phase A can enumerate (current threshold: 16).
"""

import subprocess
import os
import time
import random
import optparse
import stat
import glob
import re
import shlex


def fmt_cmd(command):
    return " ".join(shlex.quote(str(c)) for c in command)


maxtimediff = 1


def unique_file(fname_begin, fname_end=".cnf", max_num_files=2700):
    counter = 1
    while True:
        fname = "out/" + fname_begin + "_" + str(counter) + fname_end
        try:
            fd = os.open(fname, os.O_CREAT | os.O_EXCL, stat.S_IREAD | stat.S_IWRITE)
            os.fdopen(fd).close()
            return str(fname)
        except OSError:
            pass
        counter += 1
        if counter > max_num_files:
            print("Cannot create unique_file, last try was: %s" % fname)
            exit(-1)


def gen_fuzz_call_brummayer(fuzzer, fname):
    seed = random.randint(0, 1000 * 1000 * 1000)
    # Mix of small and larger CNFs.
    #
    # Half the iterations use small CNFs (~4 leaves, ~12 nodes), which
    # produce CNFs whose orig-sampling projection fits under Phase A's
    # 16-input enumeration threshold. The other half use larger CNFs
    # (~12 leaves, ~30 nodes) so the projection often EXCEEDS the
    # threshold — forcing the run past Phase A and Phase B into Phase
    # C+D, the actual CADET-flavored part. -i = leaves, -I = inner
    # nodes (see cnf-fuzz-brummayer.py).
    if random.choice([True, False]):
        call = "{0} -s {1} -i 4 -I 12 > {2}".format(fuzzer, seed, fname)
    else:
        call = "{0} -s {1} -i 12 -I 30 > {2}".format(fuzzer, seed, fname)
    return call


def add_projection(fname):
    """Append a `c p show ...` projection. Returns the projection list,
    or None if the CNF is too small to project meaningfully.

    Sometimes clamps the projection to <= 14 inputs (Phase A-friendly);
    sometimes lets it go larger (up to n_vars - 1) so Phase A's
    threshold is exceeded and the run is forced into Phase B / C+D,
    the actual CADET part of the pipeline."""
    n_vars = 0
    with open(fname, "r") as f:
        for line in f:
            line = line.strip()
            if len(line) < 3:
                continue
            if line[0] == "p":
                parts = line.split(" ")
                assert parts[1].strip() == "cnf"
                n_vars = int(parts[2])
                break

    if n_vars == 0:
        print("ERROR: Can't find 'p cnf' in file %s" % fname)
        exit(-1)
    if n_vars < 2:
        return None

    # Half the time, clamp projection size to <= 14 (Phase A's
    # enumeration is tractable). The other half: pick from a wider
    # range so Phase A is forced to bail and Phase C+D get exercised.
    if random.choice([True, False]):
        upper = max(1, min(14, n_vars - 1))
    else:
        upper = max(1, n_vars - 1)
    num = random.randint(1, upper)
    proj_set = set()
    while len(proj_set) < num:
        proj_set.add(random.randint(1, n_vars))
    proj = sorted(proj_set)

    with open(fname, "a") as f:
        f.write("c p show " + " ".join(str(a) for a in proj) + " 0\n")
    return proj


def set_up_parser():
    parser = optparse.OptionParser(usage="usage: %prog [options]",
                                   description="Fuzz the CADET synthesis path (--cadet 1)")
    parser.add_option("--verbose", "-v", action="store_true", default=False,
                      dest="verbose", help="Print more output")
    parser.add_option("--seed", dest="rnd_seed",
                      help="Start seed (random if omitted)", type=int)
    parser.add_option("--tout", "-t", dest="maxtime", type=int, default=20,
                      help="Per-iteration wall time (s). Default: %default")
    parser.add_option("--num", "-n", dest="num", type=int, default=None,
                      help="Number of iterations; unlimited if omitted")
    return parser


def run(command):
    print("--> Executing: %s" % fmt_cmd(command))
    p = subprocess.Popen(command, stderr=subprocess.STDOUT,
                         stdout=subprocess.PIPE, universal_newlines=True)
    try:
        out, err = p.communicate(timeout=options.maxtime)
    except subprocess.TimeoutExpired:
        p.kill()
        out, err = p.communicate()
        out = "TIMEOUT: Process killed after %d seconds\n" % options.maxtime + out
    return out, err, p.returncode


def run_check(command, final, seed):
    p = subprocess.Popen(command, stderr=subprocess.STDOUT,
                         stdout=subprocess.PIPE, universal_newlines=True)
    try:
        out, _err = p.communicate()
    except Exception:
        p.kill()
        print("ERROR: check process failed")
        exit(-1)

    if p.returncode < 0 or p.returncode > 1:
        print("=" * 60)
        print("BUG: test-synth crashed with returncode %d" % p.returncode)
        print("Command was: %s" % fmt_cmd(command))
        print(out)
        print("REPRODUCE: python3 ../scripts/fuzz_cadet.py --seed %d --num 1" % seed)
        print("=" * 60)
        exit(-1)

    ok = False
    for line in out.split("\n"):
        if "INCORRECT" in line:
            print("=" * 60)
            print("BUG: test-synth reported AIGs are INCORRECT")
            print("Command was: %s" % fmt_cmd(command))
            print(out)
            print("REPRODUCE: python3 ../scripts/fuzz_cadet.py --seed %d --num 1" % seed)
            print("=" * 60)
            exit(-1)
        if "CORRECT" in line and "INCORRECT" not in line:
            print("Check output: %s" % line)
            ok = True
    if not ok and final:
        print("=" * 60)
        print("BUG: check process did not report CORRECT")
        print("Command was: %s" % fmt_cmd(command))
        print(out)
        print("REPRODUCE: python3 ../scripts/fuzz_cadet.py --seed %d --num 1" % seed)
        print("=" * 60)
        exit(-1)


def run_synth(solver, fname):
    curr_time = time.time()
    toexec = solver.split()
    toexec.append(fname)
    out, err, returncode = run(toexec)
    if err is not None:
        print("Error string is: ", err)
        return True, []

    diff_time = time.time() - curr_time
    if diff_time > options.maxtime - maxtimediff:
        print("Too much time, aborted")
        return None, []

    # Exit code 42 = cadet hit a "LIMITATION" (known capability gap,
    # not a bug). Handle BEFORE the generic returncode != 0 check;
    # otherwise that path treats it as a crash. The limitation is
    # documented in cadet.cpp; the user wants the fuzzer to exercise
    # (not gate on) those cases. The print confirms it surfaced.
    if returncode == 42:
        for line in out.split("\n"):
            if "LIMITATION" in line:
                print("[skip] " + line.strip())
                break
        return False, []  # soft skip; no AIGs to check

    if returncode != 0 and not out.startswith("TIMEOUT"):
        print("Solver crashed with exit code %d" % returncode)
        print(out)
        return True, []

    aigs = []
    for line in out.split("\n"):
        line = line.strip()
        if "Training error" not in line:
            if "ERROR" in line or "Error" in line or "error" in line:
                print("Error line from solver: %s" % line)
                return True, []
            if "assert" in line or "Assertion" in line:
                print("Error line from solver: %s" % line)
                return True, []
        if line.startswith("c o Wrote AIG defs:"):
            aigs.append(line[len("c o Wrote AIG defs:"):].strip())
    return False, aigs


def is_unsat(fname):
    unsat_check = "../../cryptominisat/build/cryptominisat5"
    toexec = unsat_check.split()
    toexec.append(fname)
    out, _err, _ = run(toexec)
    for line in out.split("\n"):
        line = line.strip()
        if line.startswith("s UNSATISFIABLE"):
            print("File %s is UNSAT" % fname)
            return True
        if line.startswith("s SATISFIABLE"):
            print("File %s is SAT" % fname)
            return False
    print("ERROR: Could not determine SAT/UNSAT for %s" % fname)
    exit(-1)


def gen_fuzz(seed):
    fname = unique_file("fuzzCadet")
    print("Seed: %d  fname: %s" % (seed, fname))
    call = gen_fuzz_call_brummayer("./cnf-fuzz-brummayer.py", fname)
    print("Calling: %s" % call)
    status = subprocess.call(call, shell=True)
    if status != 0:
        print("Failed fuzzer file generator call: %s" % call)
        exit(-1)
    return fname


def cleanup(fname, prefix):
    try:
        os.unlink(fname)
    except OSError:
        pass
    for file_path in glob.glob(os.path.join(".", f"{prefix}*.aig")):
        if os.path.isfile(file_path):
            os.remove(file_path)
    for file_path in glob.glob(f"{prefix}-core-*.cnf"):
        if os.path.isfile(file_path):
            os.remove(file_path)
    try:
        os.unlink(prefix)
    except OSError:
        pass


if __name__ == "__main__":
    if os.path.exists("out") and os.path.isfile("out"):
        print("ERROR: file 'out' exists, but we need a directory named 'out'")
        exit(-1)
    os.makedirs("out", exist_ok=True)

    parser = set_up_parser()
    (options, args) = parser.parse_args()

    if options.rnd_seed is None:
        rnd_seed = int.from_bytes(os.urandom(8))
        print("Using seed:", rnd_seed)
    else:
        rnd_seed = options.rnd_seed
    random.seed(rnd_seed)

    i = 0
    while options.num is None or i < options.num:
        i += 1
        if options.rnd_seed is None:
            seed = int.from_bytes(os.urandom(8))
            random.seed(seed)
        else:
            seed = options.rnd_seed

        fname = gen_fuzz(seed)
        if add_projection(fname) is None:
            print("CNF too small, skipping")
            os.unlink(fname)
            continue
        if is_unsat(fname):
            print("UNSAT, skipping")
            os.unlink(fname)
            continue

        prefix = unique_file("fuzzCadet")
        solver = "./arjun --verb 1 --debugsynth %s " % prefix
        if random.choice([True, False]):
            solver += "--synth "
        else:
            solver += "--synthmore "
        solver += "--cadet 1 "

        # Preprocessing toggles. We want to exercise cadet both with
        # and without the upstream pipeline:
        #   - 50% of iterations: force EVERY toggleable pass OFF so
        #     cadet has to actually do the synthesis (otherwise BVE +
        #     autarky finish it first on fuzzer-sized CNFs).
        #   - 50% of iterations: pick each toggle independently, biased
        #     80/20 toward off. Some preprocessing still runs and the
        #     pipeline's downstream cadet sees the post-preprocessing
        #     CNF — which is what real-world usage looks like.
        prep_opts = [" --synthbve", " --autarky", " --extend", " --minimize",
                     " --unatedef", " --unatedefeq", " --unatedefeqnoninp",
                     " --unatedefrep"]
        if random.choice([True, False]):
            for opt in prep_opts:
                solver += opt + " 0"
        else:
            for opt in prep_opts:
                solver += opt + " " + str(random.choices([0, 1], weights=[4, 1])[0])

        err, aigs = run_synth(solver, fname)
        if err is None:
            print("Synthesis timed out on %s" % fname)
            cleanup(fname, prefix)
            continue
        if err:
            print("Synthesis failed on %s" % fname)
            print("=" * 60)
            print("REPRODUCE: python3 ../scripts/fuzz_cadet.py --seed %d --num 1" % seed)
            print("=" * 60)
            exit(-1)

        # No AIGs means run_synth returned a soft skip (cadet
        # LIMITATION, exit code 42). The skip line was already printed
        # by run_synth; just move on to the next iteration.
        if len(aigs) == 0:
            cleanup(fname, prefix)
            continue

        print("Synthesis succeeded on %s, AIGs: %s" % (fname, aigs))

        for aig in aigs:
            final = "final" in aig
            if final:
                call = "./test-synth -u -v -s %d %s %s" % (seed, fname, aig)
            else:
                call = "./test-synth -v -s %d %s %s" % (seed, fname, aig)
            print("Check: %s" % call)
            run_check(call.split(), final, seed)
            os.unlink(aig)
        cleanup(fname, prefix)
    exit(0)
