#!/usr/bin/env python3
# Runs `arjun --2qbf` and cadet on QDIMACS files and compares the verdicts.
# Run from build/:  ../scripts/bench_2qbf.py -t 20 ~/media/qbf/2qbf/qbfeval16/*.qdimacs

import argparse
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor

VERDICT = {10: "TRUE", 20: "FALSE"}


def run(cmd, tout):
    start = time.time()
    try:
        ret = subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                             timeout=tout).returncode
    except subprocess.TimeoutExpired:
        return "TOUT", tout
    return VERDICT.get(ret, "ERR(%d)" % ret), time.time() - start


def bench(fname):
    res = [run(args.arjun.split() + [fname], args.tout)]
    if args.cadet:
        res.append(run([args.cadet, fname], args.tout))
    return fname, res


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("files", nargs="+")
    parser.add_argument("-t", "--tout", type=int, default=20)
    parser.add_argument("-j", "--jobs", type=int, default=2)
    parser.add_argument("--arjun", default="./arjun --2qbf --verb 0")
    parser.add_argument("--cadet", default="../../cadet/cadet", help="'' to skip cadet")
    args = parser.parse_args()

    solved = [0, 0]
    tot_time = [0.0, 0.0]
    mismatch = 0
    with ThreadPoolExecutor(args.jobs) as pool:
        for fname, res in pool.map(bench, args.files):
            line = ""
            for i, (verdict, t) in enumerate(res):
                line += "%-8s %7.2f  " % (verdict, t)
                solved[i] += verdict in VERDICT.values()
                tot_time[i] += t
            verdicts = set(v for v, _ in res if v in VERDICT.values())
            if len(verdicts) > 1:
                mismatch += 1
                line += "MISMATCH "
            print(line + fname.split("/")[-1])
            sys.stdout.flush()
    print("arjun solved: %d T: %.1f" % (solved[0], tot_time[0]))
    if args.cadet:
        print("cadet solved: %d T: %.1f" % (solved[1], tot_time[1]))
    print("mismatches: %d of %d files" % (mismatch, len(args.files)))
    exit(1 if mismatch else 0)
