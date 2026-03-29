#!/usr/bin/env python3
# -*- coding: utf-8 -*-

# Test script for --checkrepair: generates small random CNFs with random
# independent sets, runs arjun synthesis with --checkrepair, and checks
# that the error formula count never increases.

import subprocess
import os
import sys
import random
import tempfile
import re
import optparse
import time
import itertools


SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
FUZZER = os.path.join(SCRIPT_DIR, "cnf-fuzz-brummayer.py")
ARJUN = os.path.join(SCRIPT_DIR, "..", "build", "arjun")
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
        "--minvars", type=int, default=3, dest="min_vars",
        help="Minimum number of input variables for the CNF generator "
             "(passed as -i to cnf-fuzz-brummayer, default: %default)")

    parser.add_option(
        "--maxvars", type=int, default=8, dest="max_vars",
        help="Maximum number of input variables for the CNF generator "
             "(passed as -I to cnf-fuzz-brummayer, default: %default)")

    parser.add_option(
        "--timeout", "-t", type=int, default=120, dest="timeout",
        help="Timeout per arjun run in seconds (default: %default)")

    parser.add_option(
        "--verbose", "-v", action="store_true", default=False, dest="verbose",
        help="Print detailed output including arjun's checkrepair lines")

    return parser


def generate_cnf(fname, seed, min_vars, max_vars):
    """Generate a random CNF using the Brummayer fuzzer."""
    cmd = [sys.executable, FUZZER, "-s", str(seed),
           "-i", str(min_vars), "-I", str(max_vars)]
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

    all_vars = list(range(1, num_vars + 1))
    # Pick between 1/5 and 1/3 of variables as independent set
    lo = max(1, num_vars // 5)
    hi = max(lo, num_vars // 3)
    num_proj = random.randint(lo, hi)
    proj = random.sample(all_vars, min(num_proj, len(all_vars)))

    with open(fname, "a") as f:
        f.write("c p show " + " ".join(str(v) for v in proj) + " 0\n")
    return proj


def is_unsat(fname):
    """Check if the CNF is UNSAT using CryptoMiniSat."""
    try:
        result = subprocess.run(
            [CMS, fname], capture_output=True, text=True, timeout=30)
        for line in result.stdout.split("\n"):
            if line.strip().startswith("s UNSATISFIABLE"):
                return True
            if line.strip().startswith("s SATISFIABLE"):
                return False
    except (subprocess.TimeoutExpired, FileNotFoundError):
        pass
    return None  # unknown


def run_arjun_checkrepair(fname, seed, timeout):
    """Run arjun with --synth --checkrepair and analyze output."""
    cmd = [
        ARJUN,
        "--synth",
        "--checkrepair",
        "--verb", "1",
        "--seed", str(seed),
        # Disable all preprocessors so manthan starts immediately
        "--bve", "0",
        "--synthbve", "0",
        "--unate", "0",
        "--autarky", "0",
        "--unatedef", "0",
        "--extend", "0",
        "--minimize", "0",
        "--samples", "0",
        fname,
    ]

    try:
        result = subprocess.run(
            cmd, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return "timeout", None

    output = result.stdout + (result.stderr or "")

    if result.returncode != 0:
        # Check for assertion failures / crashes
        for line in output.split("\n"):
            if "assert" in line.lower() or "Assertion" in line:
                return "crash", output
        return "error", output

    # Look for checkrepair output
    increased = False
    decreased_count = 0
    unchanged_count = 0
    counts = []
    for line in output.split("\n"):
        if "manthan-checkrepair" in line and "Error formula count:" in line:
            m = re.search(r"Error formula count:\s*(\d+)", line)
            if m:
                counts.append(int(m.group(1)))
        if "ERROR [manthan-checkrepair] Error count INCREASED" in line:
            increased = True
        if "checkrepair] Error count decreased" in line:
            decreased_count += 1
        if "checkrepair] Error count UNCHANGED" in line:
            unchanged_count += 1

    return {
        "increased": increased,
        "counts": counts,
        "decreased": decreased_count,
        "unchanged": unchanged_count,
        "output": output,
    }, None


def main():
    parser = set_up_parser()
    options, _ = parser.parse_args()

    if options.seed is not None:
        random.seed(options.seed)
    else:
        random.seed(42)

    if not os.path.isfile(ARJUN):
        print("ERROR: arjun binary not found at %s" % ARJUN)
        sys.exit(1)
    if not os.path.isfile(FUZZER):
        print("ERROR: fuzzer not found at %s" % FUZZER)
        sys.exit(1)

    stats = {
        "total": 0,
        "skipped_unsat": 0,
        "timeout": 0,
        "crash": 0,
        "no_repair": 0,
        "ok_decreased": 0,
        "bad_increased": 0,
    }

    num = options.num_runs
    if num == -1:
        print("Running indefinitely with --checkrepair "
              "(vars %d-%d, timeout %ds)...\n"
              % (options.min_vars, options.max_vars, options.timeout))
        counter = itertools.count(1)
    else:
        print("Running %d tests with --checkrepair "
              "(vars %d-%d, timeout %ds)...\n"
              % (num, options.min_vars, options.max_vars, options.timeout))
        counter = range(1, num + 1)

    with tempfile.TemporaryDirectory(prefix="checkrepair_") as tmpdir:
        for i in counter:
            seed = random.randint(0, 10**9)
            fname = os.path.join(tmpdir, "test_%d.cnf" % i)
            label = "[%d]" % i if num == -1 else "[%d/%d]" % (i, num)

            print("%s seed=%d " % (label, seed), end="", flush=True)

            generate_cnf(fname, seed, options.min_vars, options.max_vars)
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
            result, error_output = run_arjun_checkrepair(
                fname, seed, options.timeout)
            elapsed = time.time() - t_start

            if result == "timeout":
                print("TIMEOUT (%.1fs)" % elapsed)
                stats["timeout"] += 1
                continue

            if result == "crash" or result == "error":
                print("CRASH/ERROR (%.1fs)" % elapsed)
                stats["crash"] += 1
                if error_output:
                    lines = error_output.strip().split("\n")
                    for line in lines[-10:]:
                        print("  | %s" % line)
                continue

            info = result
            counts = info["counts"]

            if len(counts) == 0:
                print("OK (no repair iterations, solved immediately) "
                      "(%.1fs)" % elapsed)
                stats["no_repair"] += 1
            elif info["increased"]:
                print("BAD - count INCREASED! counts=%s (%.1fs)"
                      % (counts, elapsed))
                stats["bad_increased"] += 1
                for line in info["output"].split("\n"):
                    if "checkrepair" in line:
                        print("  | %s" % line.strip())
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

    print("\n" + "=" * 60)
    print("Results:")
    print("  Total runs with repair: %d" % stats["total"])
    print("  Skipped (UNSAT):        %d" % stats["skipped_unsat"])
    print("  Timeout:                %d" % stats["timeout"])
    print("  Crash/Error:            %d" % stats["crash"])
    print("  No repair needed:       %d" % stats["no_repair"])
    print("  OK (monotone decrease): %d" % stats["ok_decreased"])
    print("  BAD (count increased):  %d" % stats["bad_increased"])
    print("=" * 60)

    if stats["bad_increased"] > 0:
        print("\nWARNING: Some runs had increasing error counts!")
        sys.exit(1)
    else:
        print("\nAll runs OK - error count never increased.")
        sys.exit(0)


if __name__ == "__main__":
    main()
