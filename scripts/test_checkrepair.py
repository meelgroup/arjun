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

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
FUZZER = os.path.join(SCRIPT_DIR, "cnf-fuzz-brummayer.py")
ARJUN = os.path.join(SCRIPT_DIR, "..", "build", "arjun")
CMS = os.path.join(SCRIPT_DIR, "..", "..", "cryptominisat", "build", "cryptominisat5")

NUM_RUNS = 30
TIMEOUT = 120  # seconds per run


def generate_cnf(fname, seed):
    """Generate a small random CNF using the Brummayer fuzzer."""
    cmd = f"{sys.executable} {FUZZER} -s {seed} -i 3 -I 8"
    with open(fname, "w") as f:
        subprocess.run(cmd.split(), stdout=f, check=True)


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
        print(f"ERROR: No 'p cnf' header in {fname}")
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


def run_arjun_checkrepair(fname, seed):
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
            cmd, capture_output=True, text=True, timeout=TIMEOUT)
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
    random.seed(42)

    if not os.path.isfile(ARJUN):
        print(f"ERROR: arjun binary not found at {ARJUN}")
        sys.exit(1)
    if not os.path.isfile(FUZZER):
        print(f"ERROR: fuzzer not found at {FUZZER}")
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

    print(f"Running {NUM_RUNS} tests with --checkrepair...\n")

    with tempfile.TemporaryDirectory(prefix="checkrepair_") as tmpdir:
        for i in range(NUM_RUNS):
            seed = random.randint(0, 10**9)
            fname = os.path.join(tmpdir, f"test_{i}.cnf")

            print(f"[{i+1}/{NUM_RUNS}] seed={seed} ", end="", flush=True)

            generate_cnf(fname, seed)
            proj = add_projection(fname)
            if proj is None:
                print("SKIP (bad CNF)")
                continue

            sat_status = is_unsat(fname)
            if sat_status is True:
                print("SKIP (UNSAT)")
                stats["skipped_unsat"] += 1
                continue
            if sat_status is None:
                print("SKIP (SAT check unknown)")
                continue

            stats["total"] += 1
            result, error_output = run_arjun_checkrepair(fname, seed)

            if result == "timeout":
                print("TIMEOUT")
                stats["timeout"] += 1
                continue

            if result == "crash" or result == "error":
                print(f"CRASH/ERROR")
                stats["crash"] += 1
                if error_output:
                    # Print last 10 lines of output for debugging
                    lines = error_output.strip().split("\n")
                    for line in lines[-10:]:
                        print(f"  | {line}")
                continue

            info = result
            counts = info["counts"]

            if len(counts) == 0:
                print(f"OK (no repair iterations, solved immediately)")
                stats["no_repair"] += 1
            elif info["increased"]:
                print(f"BAD - count INCREASED! counts={counts}")
                stats["bad_increased"] += 1
                # Print relevant output lines
                for line in info["output"].split("\n"):
                    if "checkrepair" in line:
                        print(f"  | {line.strip()}")
            else:
                print(f"OK (counts={counts}, "
                      f"decreased={info['decreased']}, "
                      f"unchanged={info['unchanged']})")
                stats["ok_decreased"] += 1

    print(f"\n{'='*60}")
    print(f"Results:")
    print(f"  Total runs with repair: {stats['total']}")
    print(f"  Skipped (UNSAT):        {stats['skipped_unsat']}")
    print(f"  Timeout:                {stats['timeout']}")
    print(f"  Crash/Error:            {stats['crash']}")
    print(f"  No repair needed:       {stats['no_repair']}")
    print(f"  OK (monotone decrease): {stats['ok_decreased']}")
    print(f"  BAD (count increased):  {stats['bad_increased']}")
    print(f"{'='*60}")

    if stats["bad_increased"] > 0:
        print("\nWARNING: Some runs had increasing error counts!")
        sys.exit(1)
    else:
        print("\nAll runs OK - error count never increased.")
        sys.exit(0)


if __name__ == "__main__":
    main()
