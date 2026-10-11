#!/usr/bin/env python3
# Compares 2QBF preprocessors: each one runs on every file, then every solver
# runs on its output. Time is preprocessing + solving. Run from build/:
#   ../scripts/bench_2qbfpre.py -t 20 ~/media/2qbf/qbfeval16/*.qdimacs

import argparse
import gzip
import os
import shutil
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor

VERDICT = {10: "T", 20: "F"}


def run(cmd, tout, stdout=subprocess.DEVNULL):
    start = time.time()
    try:
        ret = subprocess.run(cmd, stdout=stdout, stderr=subprocess.DEVNULL,
                             timeout=tout).returncode
    except subprocess.TimeoutExpired:
        return None, tout
    return ret, time.time() - start


def size(fname):
    with open(fname) as f:
        for line in f:
            if line.startswith("p cnf"):
                return line.split()[2:4]
    return ["?", "?"]


# per preprocessor: (verdict or None, time, [per solver (verdict, time)])
def bench(orig_fname):
    fname = orig_fname
    if fname.endswith(".gz"):
        fname = os.path.join(tmpdir, os.path.basename(fname)[:-3])
        with gzip.open(orig_fname, "rb") as f, open(fname, "wb") as f2:
            shutil.copyfileobj(f, f2)
    res = []
    for name, cmd in pres:
        out = os.path.join(tmpdir, "%s-%s" % (name, os.path.basename(fname)))
        if cmd is None:
            ret, t, out = 0, 0.0, fname
        elif "%o" in cmd:
            ret, t = run([fname if x == "%i" else out if x == "%o" else x for x in cmd.split()],
                         args.pretout)
        else:
            with open(out, "w") as f:
                ret, t = run(cmd.split() + [fname], args.pretout, f)
        if ret == 0 and name == "arjun+bloqqer":
            out2 = out + "-bloqqer"
            with open(out2, "w") as f:
                ret, t2 = run(args.bloqqer.split() + [out], args.pretout, f)
            os.replace(out2, out)
            t += t2
        if ret not in (0, 10, 20):
            res.append(("-" if ret is None else "ERR(%d)" % ret, t, None, []))
            continue
        solved = []
        for _, solver in solvers:
            if ret in VERDICT:
                solved.append((VERDICT[ret], t))
                continue
            sret, st = run(solver.split() + [out], args.tout)
            solved.append((VERDICT.get(sret, "-" if sret is None else "ERR(%d)" % sret), t + st))
        res.append((VERDICT.get(ret, ""), t, size(out), solved))
        if cmd is not None:
            os.unlink(out)
    if fname != orig_fname:
        os.unlink(fname)
    return fname, res


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("files", nargs="+")
    parser.add_argument("-t", "--tout", type=int, default=20, help="per solver run")
    parser.add_argument("--pretout", type=int, default=60, help="per preprocessor run")
    parser.add_argument("-j", "--jobs", type=int, default=2)
    parser.add_argument("--arjun", default="./arjun --2qbfpre --verb 0 %i %o",
                        help="%%i and %%o are the input and output file; '' to skip")
    parser.add_argument("--bloqqer", default="../../bloqqer/bloqqer", help="'' to skip")
    parser.add_argument("--chain", action="store_true", help="also bloqqer on arjun's output")
    parser.add_argument("--cadet", default="../../cadet/cadet", help="'' to skip")
    parser.add_argument("--rareqs", default="../../rareqs-1.1/rareqs", help="'' to skip")
    args = parser.parse_args()

    pres = [("none", None)]
    pres += [(n, c) for n, c in (("bloqqer", args.bloqqer), ("arjun", args.arjun)) if c]
    if args.chain and args.arjun and args.bloqqer:
        pres.append(("arjun+bloqqer", args.arjun))
    solvers = [(n, c) for n, c in (("cadet", args.cadet), ("rareqs", args.rareqs)) if c]
    tmpdir = tempfile.mkdtemp(prefix="bench_2qbfpre_")

    by_pre = {n: 0 for n, _ in pres}
    pre_time = {n: 0.0 for n, _ in pres}
    num_solved = {(p, s): 0 for p, _ in pres for s, _ in solvers}
    tot_time = dict.fromkeys(num_solved, 0.0)
    mismatch = 0
    print("per preprocessor: verdict-if-solved pre-time vars/cls, then per solver verdict total-time")
    with ThreadPoolExecutor(args.jobs) as pool:
        for fname, res in pool.map(bench, args.files):
            line = ""
            verdicts = set()
            for (pre, _), (verdict, t, sz, solved) in zip(pres, res):
                line += "%s: %-2s %6.2f %13s " % (pre, verdict, t, "/".join(sz) if sz else "")
                by_pre[pre] += verdict in VERDICT.values()
                pre_time[pre] += t
                for (solver, _), (sverdict, st) in zip(solvers, solved):
                    line += "%-2s %6.2f " % (sverdict, st)
                    if sverdict in VERDICT.values():
                        num_solved[(pre, solver)] += 1
                        tot_time[(pre, solver)] += st
                        verdicts.add(sverdict)
                line += "| "
            if len(verdicts) > 1:
                mismatch += 1
                line += "MISMATCH "
            print(line + os.path.basename(fname))
            sys.stdout.flush()
    shutil.rmtree(tmpdir)

    for pre, _ in pres:
        print("%-8s solved alone: %4d  pre T: %8.1f" % (pre, by_pre[pre], pre_time[pre]))
        for solver, _ in solvers:
            print("  + %-7s solved: %4d  T of solved: %8.1f"
                  % (solver, num_solved[(pre, solver)], tot_time[(pre, solver)]))
    print("mismatches: %d of %d files" % (mismatch, len(args.files)))
    exit(1 if mismatch else 0)
