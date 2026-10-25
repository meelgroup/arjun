#!/usr/bin/env python3
# -*- coding: utf-8 -*-

# Fuzzes --checkrepair: the error formula count must never increase, and the
# final AIGs must be correct (test-synth -u). Stops at the first failure.

import subprocess
import os
import sys
import random
import tempfile
import re
import optparse
import time
import itertools
import shlex
import shutil


SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
FUZZER = os.path.join(SCRIPT_DIR, "cnf-fuzz-brummayer.py")
CMS = os.path.join(SCRIPT_DIR, "..", "..", "cryptominisat", "build", "cryptominisat5")


def set_up_parser():
    usage = "usage: %prog [options]"
    desc = ("Generate random CNFs, run arjun --synth --checkrepair, and "
            "verify the error formula count monotonically decreases.")

    parser = optparse.OptionParser(usage=usage, description=desc)

    parser.add_option(
        "--num", "-n", type=int, default=-1, dest="num_runs",
        help="Number of test runs, -1 for infinite (default: %default)")

    parser.add_option(
        "--seed", type=int, default=None, dest="seed",
        help="Random seed for reproducibility (default: random)")

    parser.add_option(
        "--minvars", type=int, default=8, dest="min_vars",
        help="Minimum number of input variables for the CNF generator "
             "(passed as -i to cnf-fuzz-brummayer, default: %default)")

    parser.add_option(
        "--maxvars", type=int, default=20, dest="max_vars",
        help="Maximum number of input variables for the CNF generator "
             "(passed as -I to cnf-fuzz-brummayer, default: %default)")

    parser.add_option(
        "--minrefs", type=int, default=1, dest="min_refs",
        help="Minimum references per variable -- higher values create "
             "deeper circuits with more clauses "
             "(passed as -r to cnf-fuzz-brummayer, default: %default)")

    parser.add_option(
        "--minrandcls", type=int, default=1, dest="min_rand_cls_pct",
        help="Minimum percentage of random clauses to add on top of "
             "structural clauses (0-100, default: %default)")

    parser.add_option(
        "--maxrandcls", type=int, default=10, dest="max_rand_cls_pct",
        help="Maximum percentage of random clauses to add on top of "
             "structural clauses (0-100, default: %default)")

    parser.add_option(
        "--mincllen", type=int, default=2, dest="min_clause_len",
        help="Minimum random clause length (default: %default)")

    parser.add_option(
        "--maxcllen", type=int, default=6, dest="max_clause_len",
        help="Maximum random clause length (default: %default)")

    parser.add_option(
        "--timeout", "-t", type=int, default=120, dest="timeout",
        help="Timeout per arjun run in seconds (default: %default)")

    parser.add_option(
        "--build", type=str, default=os.path.join(SCRIPT_DIR, "..", "build"),
        dest="build", help="Build dir with arjun and test-synth (default: %default)")

    parser.add_option(
        "--verbose", "-v", action="store_true", default=False, dest="verbose",
        help="Print detailed output including arjun's checkrepair lines")

    return parser


def generate_cnf(fname, seed, options):
    """Generate a random CNF using the Brummayer fuzzer."""
    cmd = [sys.executable, FUZZER, "-s", str(seed),
           "-i", str(options.min_vars), "-I", str(options.max_vars),
           "-r", str(options.min_refs),
           "-p", str(options.min_rand_cls_pct),
           "-P", str(options.max_rand_cls_pct),
           "-l", str(options.min_clause_len),
           "-L", str(options.max_clause_len)]
    with open(fname, "w") as f:
        subprocess.run(cmd, stdout=f, check=True)


def add_projection(fname):
    """Add a random independent set (projection) to the CNF file."""
    num_vars = 0
    with open(fname, "r") as f:
        for line in f:
            line = line.strip()
            if line.startswith("p cnf"):
                parts = line.split()
                num_vars = int(parts[2])
                break

    if num_vars == 0:
        print("ERROR: No 'p cnf' header in %s" % fname)
        return None
    # Synthesis needs ≥1 var NOT in the projection. With only 1 var the
    # projection necessarily covers everything; arjun would then abort with
    # "no defined vars to synthesize" — skip such degenerate CNFs.
    if num_vars < 2:
        return None

    all_vars = list(range(1, num_vars + 1))
    # Pick between 1/5 and 1/3 of variables as independent set
    lo = max(1, num_vars // 5)
    hi = max(lo, num_vars // 3)
    # Clamp upper bound to num_vars-1 so the projection is a proper subset.
    num_proj = min(num_vars - 1, random.randint(lo, hi))
    proj = random.sample(all_vars, min(num_proj, len(all_vars)))

    with open(fname, "a") as f:
        f.write("c p show " + " ".join(str(v) for v in proj) + " 0\n")
    return proj


def is_unsat(fname):
    """Check if the CNF is UNSAT using CryptoMiniSat."""
    try:
        result = subprocess.run(
            [CMS, fname], capture_output=True, text=True, timeout=30)
    except subprocess.TimeoutExpired:
        return None
    for line in result.stdout.split("\n"):
        if line.strip().startswith("s UNSATISFIABLE"):
            return True
        if line.strip().startswith("s SATISFIABLE"):
            return False
    print("ERROR: cryptominisat gave no answer on %s:\n%s" % (fname, result.stdout))
    sys.exit(1)


def run_arjun_checkrepair(arjun, fname, seed, timeout):
    """Run arjun with --synth --checkrepair and analyze output.
    Returns (result_dict_or_string, output_or_None, cmd_list)."""
    cmd = [
        arjun,
        "--synth",
        "--checkrepair",
        "--verb", "1",
        "--seed", str(seed),
        # Disable all preprocessors so cegr starts immediately
        "--bve", "0",
        "--synthpuura", "0",
        "--autarky", "0",
        "--unatedef", "0",
        "--extend", "0",
        "--backward", "0",
        "--samples", "0",
        "--cover", "0",
        "--bruteforcesynth", "0",
        fname,
        fname + "-out.aig",
    ]

    try:
        result = subprocess.run(
            cmd, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return "timeout", None, cmd

    output = result.stdout + (result.stderr or "")

    if result.returncode != 0:
        return "crash", output, cmd

    # Look for checkrepair output
    increased = False
    decreased_count = 0
    unchanged_count = 0
    counts = []
    for line in output.split("\n"):
        if "cegr-checkrepair" in line and "Error formula count:" in line:
            m = re.search(r"Error formula count:\s*(\d+)", line)
            if m:
                counts.append(int(m.group(1)))
        if "ERROR" in line:
            increased = True
        if "checkrepair] Error count decreased" in line:
            decreased_count += 1
        if "checkrepair] Error count UNCHANGED" in line:
            unchanged_count += 1

    if any(b >= a for a, b in zip(counts, counts[1:])):
        increased = True

    return {
        "increased": increased,
        "wrote_aig": any(l.startswith("c o Wrote AIG defs:") for l in output.split("\n")),
        "counts": counts,
        "decreased": decreased_count,
        "unchanged": unchanged_count,
        "output": output,
    }, None, cmd


def fail(what, fname, seed, cmd, output):
    saved = "fail_repair_%d.cnf" % seed
    shutil.copy2(fname, saved)
    print("\n%s. Saved CNF to: %s" % (what, os.path.abspath(saved)))
    print("Reproduce with:\n  %s" % " ".join(shlex.quote(str(c)) for c in cmd[:-2] + [saved, saved + "-out.aig"]))
    if output:
        print("\nLast lines of output:")
        for line in output.strip().split("\n")[-25:]:
            print("  | %s" % line)
    sys.exit(1)


def main():
    parser = set_up_parser()
    options, _ = parser.parse_args()

    if options.seed is not None:
        rnd_seed = options.seed
    else:
        rnd_seed = int.from_bytes(os.urandom(8))
        print("Using random seed: %d" % rnd_seed)
    random.seed(rnd_seed)

    arjun = os.path.join(options.build, "arjun")
    test_synth = os.path.join(options.build, "test-synth")
    for f in (arjun, test_synth, CMS):
        if not os.path.isfile(f):
            print("ERROR: %s not found" % f)
            sys.exit(1)
    if not os.path.isfile(FUZZER):
        print("ERROR: fuzzer not found at %s" % FUZZER)
        sys.exit(1)

    stats = {
        "total": 0,
        "skipped_unsat": 0,
        "timeout": 0,
        "no_repair": 0,
        "ok_decreased": 0,
    }

    num = options.num_runs
    desc = ("vars %d-%d, refs %d, rand-cls %d-%d%%, cl-len %d-%d, timeout %ds"
            % (options.min_vars, options.max_vars, options.min_refs,
               options.min_rand_cls_pct, options.max_rand_cls_pct,
               options.min_clause_len, options.max_clause_len,
               options.timeout))
    if num == -1:
        print("Running indefinitely with --checkrepair (%s)...\n" % desc)
        counter = itertools.count(1)
    else:
        print("Running %d tests with --checkrepair (%s)...\n" % (num, desc))
        counter = range(1, num + 1)

    with tempfile.TemporaryDirectory(prefix="checkrepair_") as tmpdir:
        for i in counter:
            seed = random.randint(0, 10**9)
            fname = os.path.join(tmpdir, "test_%d.cnf" % i)
            label = "[%d]" % i if num == -1 else "[%d/%d]" % (i, num)

            print("%s seed=%d " % (label, seed), end="", flush=True)

            generate_cnf(fname, seed, options)
            proj = add_projection(fname)
            if proj is None:
                print("SKIP (bad CNF)")
                continue

            if options.verbose:
                # Count vars/clauses for context
                with open(fname) as f:
                    for line in f:
                        if line.startswith("p cnf"):
                            print("(%s, proj=%d) " % (
                                line.strip(), len(proj)), end="", flush=True)
                            break

            sat_status = is_unsat(fname)
            if sat_status is True:
                print("SKIP (UNSAT)")
                stats["skipped_unsat"] += 1
                continue
            if sat_status is None:
                print("SKIP (SAT check unknown)")
                continue

            stats["total"] += 1
            t_start = time.time()
            result, error_output, cmd = run_arjun_checkrepair(
                arjun, fname, seed, options.timeout)
            elapsed = time.time() - t_start

            if result == "timeout":
                print("TIMEOUT (%.1fs)" % elapsed)
                stats["timeout"] += 1
                continue

            if result == "crash":
                print("CRASH (%.1fs)" % elapsed)
                fail("Arjun crashed", fname, seed, cmd, error_output)

            info = result
            counts = info["counts"]

            if info["increased"]:
                print("BAD - ERROR line, or count did not strictly decrease! counts=%s (%.1fs)"
                      % (counts, elapsed))
                fail("Bad repair", fname, seed, cmd,
                     "\n".join(l for l in info["output"].split("\n") if "checkrepair" in l or "ERROR" in l))
            elif len(counts) == 0:
                print("OK (no repair iterations, solved immediately) "
                      "(%.1fs)" % elapsed)
                stats["no_repair"] += 1
            else:
                print("OK (counts=%s, decreased=%d, unchanged=%d) "
                      "(%.1fs)"
                      % (counts, info["decreased"], info["unchanged"],
                         elapsed))
                stats["ok_decreased"] += 1

            if options.verbose:
                for line in info["output"].split("\n"):
                    if "checkrepair" in line:
                        print("  | %s" % line.strip())

            if not info["wrote_aig"]:
                fail("Arjun wrote no AIG", fname, seed, cmd, info["output"])
            check = subprocess.run([test_synth, "-u", "-s", str(seed), fname, fname + "-out.aig"],
                                   capture_output=True, text=True)
            if check.returncode != 0 or "AIGs are verified CORRECT" not in check.stdout:
                fail("test-synth rejected the AIGs", fname, seed, cmd, check.stdout + check.stderr)

    print("\n" + "=" * 60)
    print("Results:")
    print("  Total runs with repair: %d" % stats["total"])
    print("  Skipped (UNSAT):        %d" % stats["skipped_unsat"])
    print("  Timeout:                %d" % stats["timeout"])
    print("  No repair needed:       %d" % stats["no_repair"])
    print("  OK (monotone decrease): %d" % stats["ok_decreased"])
    print("=" * 60)

    print("\nAll runs OK - error count never increased, AIGs correct.")


if __name__ == "__main__":
    main()
