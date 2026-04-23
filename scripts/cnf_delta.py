#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
cnf_delta.py — clause-level delta debugger for DIMACS CNFs.

Given a CNF file and an oracle command that reports FAIL (non-zero exit OR a
specific match token in stdout) on the current CNF, iteratively remove
clauses while preserving FAIL. Outputs the minimized CNF and reports the
round-by-round shrink.

Non-clause lines ("c ..." comments, "p cnf ...", and especially the
"c p show ... 0" projection line that arjun requires) are preserved
verbatim. Only clause lines are candidates for removal.

Strategy is plain ddmin: partition clauses into granularity chunks, try
removing each chunk; if that fails, try keeping only each chunk; double
granularity on no progress. Terminates when the chunk size is 1 and no
removals at granularity == len(clauses) succeeded.

Typical usage:

    # Oracle that returns 0 (bug reproduces) iff arjun aborts with the target
    # assertion text.
    cat > /tmp/oracle.sh <<'SH'
    #!/bin/bash
    out=$(timeout 30 /path/to/arjun --verb 0 --synthmore ... "$1" 2>&1)
    if [[ "$out" == *"Assertion \`incorrect.empty()'"* ]]; then
        exit 0
    fi
    exit 1
    SH
    chmod +x /tmp/oracle.sh

    ./cnf_delta.py /tmp/bug2.cnf /tmp/bug2_min.cnf /tmp/oracle.sh
"""

import argparse
import os
import shutil
import subprocess
import sys
import tempfile
from typing import List, Tuple


def parse_cnf(path: str) -> Tuple[List[str], List[List[int]], List[str]]:
    """Return (header_lines, clauses, trailer_lines).

    Header lines are everything up to and including the `p cnf` line.
    Trailer lines are comment lines after the clauses (notably `c p show`).
    Clauses are the numeric DIMACS clauses (each a list of ints, 0-terminator
    stripped).

    Any non-clause line interleaved with clauses goes into trailer (preserved
    after all clauses). This is good enough for arjun CNFs in practice.
    """
    header: List[str] = []
    trailer: List[str] = []
    clauses: List[List[int]] = []
    saw_p = False
    with open(path) as f:
        for raw in f:
            line = raw.rstrip("\n")
            stripped = line.strip()
            if not stripped:
                if saw_p:
                    trailer.append(line)
                else:
                    header.append(line)
                continue
            if stripped.startswith("c") or stripped.startswith("p"):
                if not saw_p:
                    header.append(line)
                    if stripped.startswith("p"):
                        saw_p = True
                else:
                    trailer.append(line)
                continue
            # numeric clause line
            parts = stripped.split()
            if parts and parts[-1] == "0":
                parts = parts[:-1]
            clauses.append([int(x) for x in parts])
    if not saw_p:
        raise RuntimeError(f"{path} has no `p cnf` header")
    return header, clauses, trailer


def write_cnf(path: str, header: List[str], clauses: List[List[int]],
              trailer: List[str]) -> None:
    # Rewrite the `p cnf NVARS NCLAUSES` line so NCLAUSES matches what we emit.
    # NVARS we preserve verbatim — arjun keeps the full var namespace even if
    # some vars become unused, which is fine for our purposes.
    new_header: List[str] = []
    for line in header:
        if line.strip().startswith("p"):
            parts = line.split()
            if len(parts) >= 4:
                parts[3] = str(len(clauses))
                new_header.append(" ".join(parts))
            else:
                new_header.append(line)
        else:
            new_header.append(line)
    with open(path, "w") as f:
        for line in new_header:
            f.write(line + "\n")
        for cl in clauses:
            f.write(" ".join(str(l) for l in cl) + " 0\n")
        for line in trailer:
            f.write(line + "\n")


def run_oracle(oracle: str, cnf_path: str, timeout: int) -> bool:
    """Return True iff the oracle reports FAIL (bug still reproduces) on
    this CNF."""
    try:
        r = subprocess.run([oracle, cnf_path],
                           stdout=subprocess.DEVNULL,
                           stderr=subprocess.DEVNULL,
                           timeout=timeout)
    except subprocess.TimeoutExpired:
        return False
    return r.returncode == 0


def ddmin_clauses(header: List[str], clauses: List[List[int]],
                  trailer: List[str], oracle: str, timeout: int,
                  scratch_dir: str) -> List[List[int]]:
    """Classic ddmin on the clause list."""
    scratch = os.path.join(scratch_dir, "candidate.cnf")
    n = len(clauses)
    granularity = 2
    iter_n = 0
    while len(clauses) >= 2:
        iter_n += 1
        step = max(len(clauses) // granularity, 1)
        # Build chunks
        chunks: List[Tuple[int, int]] = []
        for start in range(0, len(clauses), step):
            chunks.append((start, min(start + step, len(clauses))))

        reduced = False

        # Phase 1: try removing each chunk
        for (a, b) in chunks:
            candidate = clauses[:a] + clauses[b:]
            if not candidate:
                continue
            write_cnf(scratch, header, candidate, trailer)
            if run_oracle(oracle, scratch, timeout):
                clauses = candidate
                granularity = max(granularity - 1, 2)
                print(f"[ddmin iter {iter_n}] REMOVED chunk [{a}:{b}] "
                      f"({b-a} cls) → {len(clauses)} remain",
                      flush=True)
                reduced = True
                break

        # Phase 2: try keeping only each chunk (complement test)
        if not reduced:
            for (a, b) in chunks:
                candidate = clauses[a:b]
                write_cnf(scratch, header, candidate, trailer)
                if run_oracle(oracle, scratch, timeout):
                    clauses = candidate
                    granularity = 2
                    print(f"[ddmin iter {iter_n}] KEPT ONLY chunk [{a}:{b}] "
                          f"→ {len(clauses)} remain",
                          flush=True)
                    reduced = True
                    break

        if not reduced:
            if granularity >= len(clauses):
                break
            granularity = min(granularity * 2, len(clauses))

    return clauses


def main() -> int:
    p = argparse.ArgumentParser(
        description="Clause-level delta debugger for DIMACS CNFs.")
    p.add_argument("cnf_in", help="Input CNF (must currently trigger the bug)")
    p.add_argument("cnf_out", help="Output path for the minimized CNF")
    p.add_argument("oracle", help="Executable path; called as `oracle <cnf>`. "
                   "Must exit 0 iff the bug reproduces on <cnf>.")
    p.add_argument("--timeout", type=int, default=30,
                   help="Per-oracle-call timeout seconds (default: 30)")
    args = p.parse_args()

    if not os.path.isfile(args.cnf_in):
        print(f"ERROR: {args.cnf_in} does not exist", file=sys.stderr)
        return 2
    if not os.access(args.oracle, os.X_OK):
        print(f"ERROR: {args.oracle} is not executable", file=sys.stderr)
        return 2

    header, clauses, trailer = parse_cnf(args.cnf_in)
    print(f"Parsed {len(clauses)} clauses from {args.cnf_in}", flush=True)

    scratch_dir = tempfile.mkdtemp(prefix="cnf_delta_")
    try:
        # Sanity: verify the input reproduces
        write_cnf(os.path.join(scratch_dir, "candidate.cnf"),
                  header, clauses, trailer)
        if not run_oracle(args.oracle,
                          os.path.join(scratch_dir, "candidate.cnf"),
                          args.timeout):
            print("ERROR: oracle does not report FAIL on the initial CNF. "
                  "Check your oracle script and timeout.", file=sys.stderr)
            return 3
        print("Initial CNF confirmed to trigger the bug.", flush=True)

        minimized = ddmin_clauses(header, clauses, trailer, args.oracle,
                                  args.timeout, scratch_dir)
        write_cnf(args.cnf_out, header, minimized, trailer)
        print(f"\nMinimized {len(clauses)} → {len(minimized)} clauses "
              f"({100.0 * len(minimized) / max(1, len(clauses)):.1f}%)")
        print(f"Written: {args.cnf_out}")
    finally:
        shutil.rmtree(scratch_dir, ignore_errors=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
