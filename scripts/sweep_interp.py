#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# Copyright (C) 2026 Mate Soos.
# License: GPL-2.0

"""
sweep_interp.py — one-knob-at-a-time sweep for the --interprepair* tunables.

Run from build/:

  ./sweep_interp.py                          # default benchmark list, default configs
  ./sweep_interp.py --configs all            # full matrix
  ./sweep_interp.py -t 60                    # 60s timeout per (cnf, config) cell
  ./sweep_interp.py --bench-list mylist.txt  # custom CNF list (one path per line)
  ./sweep_interp.py --csv out.csv            # also dump raw rows to CSV
  ./sweep_interp.py --jobs 4                 # run 4 cells in parallel

Output is a table: one row per (cnf, config), baseline first.
"""

import os
import sys
import re
import time
import argparse
import subprocess
import csv
from dataclasses import dataclass, field, asdict
from typing import Dict, List, Optional, Tuple
from concurrent.futures import ThreadPoolExecutor, as_completed


# Default benchmark set; override with --bench-list.
DEFAULT_BENCH = [
    "benchmarks-qdimacs/stmt17_70_98.qdimacs.cnf",
    "benchmarks-qdimacs/stmt19_64_91.qdimacs.cnf",
    "benchmarks-qdimacs/stmt19_71_95.qdimacs.cnf",
    "benchmarks-qdimacs/stmt19_75_83.qdimacs.cnf",
    "benchmarks-qdimacs/stmt25_52_53.qdimacs.cnf",
    "benchmarks-qdimacs/sdlx-fixpoint-3.qdimacs.cnf",
    "benchmarks-qdimacs/sdlx-fixpoint-4.qdimacs.cnf",
    "benchmarks-qdimacs/driver_a9n.sat.qdimacs.cnf",
    "benchmarks-qdimacs/driver_a10y.sat.qdimacs.cnf",
    "benchmarks-qdimacs/factorization8.qdimacs.cnf",
    "benchmarks-qdimacs/amba2c7n.sat.qdimacs.cnf",
]


# Config matrix: (name, arjun flags). First entry is the baseline;
# each other isolates one knob.
QUICK_CONFIGS: List[Tuple[str, str]] = [
    ("baseline",         "--interprepair 0"),
    ("interp-default",   "--interprepair 1"),
    ("mincl-8",          "--interprepair 2 --interprepairmincl 8"),
    ("minvar-5",         "--interprepair 1 --interprepairminvar 5"),
    ("uncond",           "--interprepair 1 --interprepairuncond 1"),
    ("b1rewrite",        "--interprepair 1 --interprepairb1rewrite 1"),
    ("b1uselit",         "--interprepair 1 --interprepairb1uselit 1"),
    ("cache-128",        "--interprepair 1 --interprepaircache 128"),
]

ALL_CONFIGS: List[Tuple[str, str]] = [
    ("baseline",         "--interprepair 0"),
    ("interp-default",   "--interprepair 1"),
    # Gating
    ("mincl-8",          "--interprepair 2 --interprepairmincl 8"),
    ("mincl-12",         "--interprepair 2 --interprepairmincl 12"),
    ("minvar-5",         "--interprepair 1 --interprepairminvar 5"),
    ("minvar-50",        "--interprepair 1 --interprepairminvar 50"),
    ("maxnodes-200",     "--interprepair 1 --interprepairmaxnodes 200"),
    ("maxnodes-2000",    "--interprepair 1 --interprepairmaxnodes 2000"),
    ("maxconfl-50k",     "--interprepair 1 --interprepairmaxconfl 50000"),
    ("adaptive",         "--interprepair 1 --interprepairadaptive 1"),
    # Solve flavour
    ("uncond",           "--interprepair 1 --interprepairuncond 1"),
    ("cache-64",         "--interprepair 1 --interprepaircache 64"),
    ("cache-512",        "--interprepair 1 --interprepaircache 512"),
    # AIG post-processing
    ("b1rewrite",        "--interprepair 1 --interprepairb1rewrite 1"),
    ("b1satsweep",       "--interprepair 1 --interprepairb1satsweep 1"),
    ("groupcse",         "--interprepair 1 --interprepairgroupcse 1"),
    ("b1uselit",         "--interprepair 1 --interprepairb1uselit 1"),
    # Combo: "kitchen sink" for benchmarks where interp shines
    ("combo-aggressive", "--interprepair 1 "
                         "--interprepairb1rewrite 1 --interprepairgroupcse 1 "
                         "--interprepaircache 128 --interprepairuncond 1"),
    # Combo: "conservative" — only fire on big conflicts, with adaptive backoff
    ("combo-conservative",
                         "--interprepair 2 --interprepairmincl 8 "
                         "--interprepairadaptive 1 --interprepairmaxconfl 50000"),
]


# ────────────────────────────────────────────────────────────────────────────
# Per-run result.
# ────────────────────────────────────────────────────────────────────────────
@dataclass
class RunResult:
    cnf: str
    config: str
    flags: str
    status: str = "ok"          # ok / timeout / error
    wall_s: float = 0.0
    arjun_total_s: float = 0.0  # "All done. T: X"
    repair_s: float = 0.0       # "[manthan] Done. ... repair T: X"
    repairs: int = 0
    loops: int = 0
    interp_pct: int = -1        # -1 if line absent (interp disabled)
    interp_calls: int = -1
    interp_cache_hits: int = -1
    interp_budget_exh: int = -1
    interp_uncond_succ: int = -1
    b1_pre: int = -1
    b1_post: int = -1
    adaptive_skips: int = -1
    err_first_line: str = ""


# ────────────────────────────────────────────────────────────────────────────
# Output parsing. The strings come from print_stats / print_detailed_stats
# in manthan.cpp. ANSI colour codes are stripped before matching.
# ────────────────────────────────────────────────────────────────────────────
ANSI_RE = re.compile(r"\x1b\[[0-9;]*[a-zA-Z]")

REP_LINE_RE = re.compile(
    r"\[manthan\]\s+rep:\s*(\d+)\s+loops:\s*(\d+).*?interp:\s*(\d+)%",
    re.DOTALL,
)
ALL_DONE_RE = re.compile(r"\[arjun\] All done\. T:\s*([0-9.]+)")
REPAIR_T_RE = re.compile(r"\[manthan\] Done\.[^\n]*repair T:\s*([0-9.]+)")
INTERP_DROVE_RE = re.compile(
    r"interp drove repairs:\s*(\d+)\s*/\s*(\d+)\s*\(([0-9.]+)%\)"
)
INTERP_CALLS_RE = re.compile(
    r"interp calls.*?:\s*(\d+).*?cache_hit:\s*(\d+).*?budget_exh:\s*(\d+)"
)
UNCOND_RE = re.compile(r"uncond succeeded:\s*(\d+)")
B1_SIMP_RE = re.compile(r"b1 simp:\s+pre=(\d+)\s+post=(\d+)")
ADAPTIVE_RE = re.compile(r"adaptive skips:\s*(\d+)")


def strip_ansi(s: str) -> str:
    return ANSI_RE.sub("", s)


def parse_output(stdout: str, stderr: str) -> Dict[str, object]:
    text = strip_ansi(stdout)
    out: Dict[str, object] = {}

    m = ALL_DONE_RE.search(text)
    if m: out["arjun_total_s"] = float(m.group(1))

    # Capture the LAST "rep:" line (the DONE one); regex is non-greedy, so we
    # search progressively.
    last_rep = None
    for m in REP_LINE_RE.finditer(text):
        last_rep = m
    if last_rep:
        out["repairs"]    = int(last_rep.group(1))
        out["loops"]      = int(last_rep.group(2))
        out["interp_pct"] = int(last_rep.group(3))

    m = REPAIR_T_RE.search(text)
    if m: out["repair_s"] = float(m.group(1))

    m = INTERP_DROVE_RE.search(text)
    if m:
        # interp_drove also gives us a confirmed interp_calls source.
        pass

    m = INTERP_CALLS_RE.search(text)
    if m:
        out["interp_calls"]      = int(m.group(1))
        out["interp_cache_hits"] = int(m.group(2))
        out["interp_budget_exh"] = int(m.group(3))

    m = UNCOND_RE.search(text)
    if m: out["interp_uncond_succ"] = int(m.group(1))

    m = B1_SIMP_RE.search(text)
    if m:
        out["b1_pre"]  = int(m.group(1))
        out["b1_post"] = int(m.group(2))

    m = ADAPTIVE_RE.search(text)
    if m: out["adaptive_skips"] = int(m.group(1))

    # First non-empty stderr line — useful when status=error.
    for ln in (stderr or "").splitlines():
        ln = ln.strip()
        if ln:
            out["err_first_line"] = ln[:200]
            break

    return out


# ────────────────────────────────────────────────────────────────────────────
# Run one (cnf, config) cell.
# ────────────────────────────────────────────────────────────────────────────
def run_cell(arjun: str, cnf: str, name: str, flags: str,
             timeout_s: int) -> RunResult:
    r = RunResult(cnf=cnf, config=name, flags=flags)
    cmd = [arjun, "--verb", "1", "--synth"] + flags.split() + [cnf]
    t0 = time.time()
    try:
        p = subprocess.run(cmd, capture_output=True, text=True,
                           timeout=timeout_s)
    except subprocess.TimeoutExpired:
        r.status = "timeout"
        r.wall_s = time.time() - t0
        return r
    except Exception as e:
        r.status = f"error:{type(e).__name__}"
        r.err_first_line = str(e)[:200]
        r.wall_s = time.time() - t0
        return r
    r.wall_s = time.time() - t0

    parsed = parse_output(p.stdout, p.stderr)
    for k, v in parsed.items():
        setattr(r, k, v)

    if p.returncode != 0:
        r.status = f"rc={p.returncode}"
        # arjun returns nonzero on assertion / crash; keep partial parse.

    return r


# ────────────────────────────────────────────────────────────────────────────
# Table printer.
# ────────────────────────────────────────────────────────────────────────────
def fmt_int(v) -> str:
    return "" if v is None or v == -1 else str(v)

def fmt_float(v, prec=2) -> str:
    return "" if v is None or v == 0.0 else f"{v:.{prec}f}"

def print_per_cnf_table(rows: List[RunResult]):
    """For each CNF: baseline first, variants sorted by repair count."""
    by_cnf: Dict[str, List[RunResult]] = {}
    for r in rows:
        by_cnf.setdefault(r.cnf, []).append(r)

    header = ("config", "status", "rep", "loops", "T-tot", "T-rep",
              "interp%", "calls", "cache_h", "bud_x", "uncond", "b1pre→post", "adapt_sk")
    widths = (24, 10, 6, 6, 8, 8, 7, 6, 7, 5, 6, 14, 8)

    def line(cols):
        return "  ".join(c.ljust(w) for c, w in zip(cols, widths))

    for cnf in sorted(by_cnf.keys()):
        cells = by_cnf[cnf]
        baseline = next((c for c in cells if c.config == "baseline"), None)
        others = sorted([c for c in cells if c.config != "baseline"],
                        key=lambda r: (r.status != "ok",
                                       r.repairs if r.status == "ok" else 1<<30,
                                       r.wall_s))
        print()
        print("═" * 116)
        print(f"== {os.path.basename(cnf)}")
        print("═" * 116)
        print(line(header))
        print("─" * 116)
        for r in ([baseline] if baseline else []) + others:
            if r is None: continue
            b1 = (f"{r.b1_pre}→{r.b1_post}" if r.b1_pre != -1 else "")
            print(line((
                r.config,
                r.status,
                fmt_int(r.repairs),
                fmt_int(r.loops),
                fmt_float(r.arjun_total_s),
                fmt_float(r.repair_s),
                fmt_int(r.interp_pct),
                fmt_int(r.interp_calls),
                fmt_int(r.interp_cache_hits),
                fmt_int(r.interp_budget_exh),
                fmt_int(r.interp_uncond_succ),
                b1,
                fmt_int(r.adaptive_skips),
            )))


def print_summary(rows: List[RunResult], configs: List[Tuple[str, str]]):
    """Aggregate: for each config, how many cnfs improved/regressed vs baseline."""
    by_cnf: Dict[str, Dict[str, RunResult]] = {}
    for r in rows:
        by_cnf.setdefault(r.cnf, {})[r.config] = r

    print()
    print("═" * 80)
    print("== SUMMARY: each config vs baseline (across all cnfs)")
    print("═" * 80)
    print(f"{'config':<24}  {'better':>7}  {'same':>5}  {'worse':>6}  "
          f"{'TO/err':>7}  {'sum-Δrep':>9}  {'sum-Δtime':>10}")
    print("─" * 80)
    for name, _ in configs:
        if name == "baseline": continue
        better = same = worse = bad = 0
        d_rep = 0; d_time = 0.0
        for cnf, cfgs in by_cnf.items():
            base = cfgs.get("baseline")
            cur  = cfgs.get(name)
            if base is None or cur is None: continue
            if cur.status != "ok" or base.status != "ok":
                bad += 1
                continue
            d_rep  += (cur.repairs - base.repairs)
            d_time += (cur.arjun_total_s - base.arjun_total_s)
            if cur.repairs < base.repairs: better += 1
            elif cur.repairs > base.repairs: worse += 1
            else: same += 1
        print(f"{name:<24}  {better:>7}  {same:>5}  {worse:>6}  "
              f"{bad:>7}  {d_rep:>+9}  {d_time:>+10.2f}")


# ────────────────────────────────────────────────────────────────────────────
# Main.
# ────────────────────────────────────────────────────────────────────────────
def main():
    ap = argparse.ArgumentParser(
        description="Sweep --interprepair* tunables across a benchmark set.")
    ap.add_argument("--arjun", default="./arjun",
                    help="path to arjun binary (default: ./arjun)")
    ap.add_argument("--bench-list", default=None,
                    help="file with one CNF path per line (default: built-in)")
    ap.add_argument("--configs", default="quick", choices=("quick", "all"),
                    help="which config matrix to run (default: quick)")
    ap.add_argument("-t", "--timeout", type=int, default=60,
                    help="per-cell timeout in seconds (default: 60)")
    ap.add_argument("--jobs", type=int, default=1,
                    help="run this many cells in parallel (default: 1)")
    ap.add_argument("--csv", default=None, help="optional CSV dump of all rows")
    args = ap.parse_args()

    if not os.path.exists(args.arjun):
        sys.exit(f"arjun binary not found at {args.arjun}; "
                 "run from build/ or pass --arjun")

    cnfs: List[str]
    if args.bench_list:
        with open(args.bench_list) as f:
            cnfs = [ln.strip() for ln in f if ln.strip() and not ln.startswith("#")]
    else:
        cnfs = DEFAULT_BENCH
    missing = [c for c in cnfs if not os.path.exists(c)]
    if missing:
        sys.exit(f"missing CNF(s): {missing[:3]}{' ...' if len(missing)>3 else ''}")

    configs = QUICK_CONFIGS if args.configs == "quick" else ALL_CONFIGS
    cells = [(cnf, name, flags) for cnf in cnfs for name, flags in configs]
    total = len(cells)

    print(f"Running {total} cells "
          f"({len(cnfs)} cnfs × {len(configs)} configs), "
          f"timeout {args.timeout}s, jobs={args.jobs}")
    rows: List[RunResult] = []
    started = time.time()

    if args.jobs <= 1:
        for i, (cnf, name, flags) in enumerate(cells, 1):
            r = run_cell(args.arjun, cnf, name, flags, args.timeout)
            rows.append(r)
            print(f"  [{i}/{total}] {os.path.basename(cnf):<40} "
                  f"{name:<20}  {r.status:<8}  "
                  f"rep={fmt_int(r.repairs):<5}  T={fmt_float(r.wall_s)}s")
    else:
        with ThreadPoolExecutor(max_workers=args.jobs) as ex:
            futs = {ex.submit(run_cell, args.arjun, c, n, f, args.timeout): (c, n)
                    for c, n, f in cells}
            done = 0
            for fut in as_completed(futs):
                r = fut.result()
                rows.append(r)
                done += 1
                print(f"  [{done}/{total}] {os.path.basename(r.cnf):<40} "
                      f"{r.config:<20}  {r.status:<8}  "
                      f"rep={fmt_int(r.repairs):<5}  T={fmt_float(r.wall_s)}s")

    print(f"\nDone in {time.time()-started:.1f}s")

    # Per-cnf tables.
    print_per_cnf_table(rows)
    # Summary.
    print_summary(rows, configs)

    if args.csv:
        with open(args.csv, "w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=list(asdict(rows[0]).keys()))
            w.writeheader()
            for r in rows: w.writerow(asdict(r))
        print(f"\nWrote {len(rows)} rows to {args.csv}")


if __name__ == "__main__":
    main()
