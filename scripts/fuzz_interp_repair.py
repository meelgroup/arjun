#!/usr/bin/env python3
# -*- coding: utf-8 -*-

# Copyright (C) 2026 Mate Soos
#
# This program is free software; you can redistribute it and/or
# modify it under the terms of the GNU General Public License
# as published by the Free Software Foundation; version 2
# of the License.

"""
Fuzzer for the Craig-interpolant repair path: like fuzz_synth but with
--interprepair always 1 or 2, so every iteration exercises it.

Usage (from build/):
    ./fuzz_interp_repair.py --num 1000
    ./fuzz_interp_repair.py --seed N --num 1   # reproduce
"""

import sys
import os
import random

# Re-use everything from fuzz_synth — we only override the flag-randomisation
# behaviour for --interprepair so that every iteration enables it.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import fuzz_synth as _fs


# Monkey-patch random.choices so the interp_repair mode never picks 0.
def _force_interp_choice():
    # Force the random.choices-call in fuzz_synth to never return 0.
    orig_choices = random.choices
    def patched_choices(population, weights=None, *, cum_weights=None, k=1):
        # Drop the 0 option from the interp_repair [0,1,2] selection.
        if (list(population) == [0, 1, 2]
                and weights is not None
                and len(weights) == 3):
            return orig_choices([1, 2], weights=[1, 1], k=k)
        return orig_choices(population, weights=weights,
                            cum_weights=cum_weights, k=k)
    random.choices = patched_choices


if __name__ == "__main__":
    _force_interp_choice()
    if os.path.exists("out") and os.path.isfile("out"):
        print("ERROR: file 'out' exists, but we need a directory named 'out'")
        sys.exit(-1)

    os.makedirs("out", exist_ok=True)
    parser = _fs.set_up_parser()
    (options, args) = parser.parse_args()
    _fs.options = options  # fuzz_synth references options as a module global

    # Mostly tiny CNFs, with a rare heavy tail so interp conflicts that
    # span y variables still get exercised.
    _orig_brummayer = _fs.gen_fuzz_call_brummayer
    def _bigger_brummayer(fuzzer, fname):
        seed = random.randint(0, 1000*1000*1000)
        profile = random.choices(
            ["tiny", "medium", "large", "huge"],
            weights=[85, 10, 4, 1])[0]
        if profile == "tiny":
            return "{0} -s {1} > {2}".format(fuzzer, seed, fname)
        if profile == "medium":
            return "{0} -s {1} -i 8 -I 15 > {2}".format(fuzzer, seed, fname)
        if profile == "large":
            return "{0} -s {1} -i 14 -I 30 > {2}".format(fuzzer, seed, fname)
        return "{0} -s {1} -i 22 -I 45 > {2}".format(fuzzer, seed, fname)
    _fs.gen_fuzz_call_brummayer = _bigger_brummayer

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

        fname = _fs.gen_fuzz(seed)
        if _fs.add_projection(fname) is None:
            print("Generated file %s has <2 vars (no defined var possible), skipping" % fname)
            os.unlink(fname)
            continue
        if _fs.is_unsat(fname):
            print("Generated file %s is UNSAT, skipping synthesis" % fname)
            os.unlink(fname)
            continue
        prefix = _fs.unique_file("fuzzInterp")
        print("Using prefix %s for synthesis output files" % prefix)

        # Minimal driver string with interpolation forced on.
        ir_mode = random.choice([1, 2])
        solver = "./arjun --verb 1 --debugsynth %s " % prefix
        # Mode toggles
        if random.choice([True, False]):
            solver += "--synth "
        else:
            solver += "--synthmore "
        # Boolean opts (a small subset; full sweep is fuzz_synth's job).
        for opt in ["--synthbve", "--extend", "--minimize", "--minimconfl",
                    "--filtersamples", "--uniqsamp", "--bwequal"]:
            solver += " %s %d" % (opt, random.choice([0, 1]))
        # CTX/repair solver picks (cadical only — tracer needs cadical anyway).
        solver += " --ctxsolver 1 --repairsolver 1"
        # The interpolation flag itself.
        solver += " --interprepair %d" % ir_mode
        if ir_mode == 2:
            solver += " --interprepairmincl %s" % random.choice(["1", "2", "4", "8", "20"])
        solver += " --interprepairmaxnodes %s" % random.choice(["0", "10", "100", "10000"])
        solver += " --interprepairb1rewrite %s" % random.choice(["0", "1"])
        solver += " --interprepairmaxconfl %s" % random.choice(["0", "100", "10000"])
        solver += " --interprepairb1satsweep %s" % random.choice(["0", "1"])
        solver += " --interprepairgroupcse %s" % random.choice(["0", "1"])
        solver += " --interprepairsystem %s" % random.choice(["0", "1"])
        solver += " --interprepairfullconf %s" % random.choice(["0", "1"])
        solver += " --interprepairadaptive %s" % random.choice(["0", "1"])
        solver += " --interprepairratioskip %s" % random.choice(["1.0", "5.0", "20.0"])
        solver += " --interprepairskipwindow %s" % random.choice(["1", "10", "100"])
        solver += " --interprepairprogressmax %s" % random.choice(["0", "1", "5", "100"])
        # Force the doubled-CNF interpolation solver to rebuild after every
        # 1..5 interpolants so the rebuild path is exercised here too.
        solver += " --interprebuildevery %d" % random.randint(1, 5)
        # Strategy
        solver += " --mstrategy " + _fs.gen_mstrategy()

        err, aigs = _fs.run_synth(solver, fname)
        if err is None:
            print("Synthesis timed out on file %s" % fname)
            _fs.cleanup(fname, prefix)
            continue
        if err:
            print("Synthesis failed on file %s" % fname)
            print("=" * 60)
            print("REPRODUCE with: python3 %s --seed %d --num 1" %
                  (os.path.basename(__file__), seed))
            print("=" * 60)
            sys.exit(-1)
        print("Synthesis succeeded on file %s, produced files: %s" %
              (fname, str(aigs)))
        if len(aigs) == 0:
            print("ERROR: Synthesis produced no output AIGs on file %s" % fname)
            sys.exit(-1)
        _fs.check_core_files(prefix)

        for aig in aigs:
            final = "final" in aig
            if final:
                call = "./test-synth -u -v -s %d %s %s" % (seed, fname, aig)
            else:
                call = "./test-synth -v -s %d %s %s" % (seed, fname, aig)
            print("Running check command: ", call)
            _fs.run_check(call.split(), final, seed)
            try: os.unlink(aig)
            except OSError: pass

        _fs.cleanup(fname, prefix)
    sys.exit(0)
