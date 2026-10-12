#!/usr/bin/env python3
# Staged 2QBF preprocessor benchmark with a result cache. Run from build/:
#   ../scripts/qbf2pre_bench/bench.py pre NAME 'cmd with %i %o'   (or cmd writing to stdout if no %o)
#   ../scripts/qbf2pre_bench/bench.py solve PRE NAME 'cmd %i'     (solve_all.sh PRE runs the four solvers)
#   ../scripts/qbf2pre_bench/bench.py report
# Files are the ones in sample.tsv (made by mksample.py). The outputs and the results are kept in
# $WORK (./qbf2pre_work): res.tsv has kind, pre, solver, file, verdict, seconds, vars, cls, lits.
# Env: PRETOUT (120), TOUT (20), JOBS (2). A finished (pre, solver, file) is never run again.
import gzip, os, shutil, subprocess, sys, time, resource
from concurrent.futures import ThreadPoolExecutor

S = os.path.dirname(os.path.abspath(__file__))
W = os.environ.get("WORK", os.path.abspath("qbf2pre_work"))
RES = os.path.join(W, "res.tsv")
PRETOUT = int(os.environ.get("PRETOUT", 120))
TOUT = int(os.environ.get("TOUT", 20))
JOBS = int(os.environ.get("JOBS", 2))
VERDICT = {10: "T", 20: "F"}
os.makedirs(W, exist_ok=True)


def base(p):
    b = os.path.basename(p)
    return b[:-3] if b.endswith(".gz") else b


# the same file can be in two sets: once is enough
def sample():
    rows, seen = [], set()
    for l in open(os.path.join(S, "sample.tsv")):
        row = l.rstrip("\n").split("\t")
        if base(row[2]) not in seen:
            seen.add(base(row[2]))
            rows.append(row)
    return rows


def plain(p):
    out = os.path.join(W, "none", base(p))
    if not os.path.exists(out):
        os.makedirs(os.path.dirname(out), exist_ok=True)
        if p.endswith(".gz"):
            with gzip.open(p, "rb") as f, open(out, "wb") as g:
                shutil.copyfileobj(f, g)
        else:
            shutil.copy(p, out)
    return out


def limits():
    resource.setrlimit(resource.RLIMIT_AS, (3 << 30, 3 << 30))


def run(cmd, tout, stdout=subprocess.DEVNULL):
    t = time.time()
    try:
        r = subprocess.run(cmd, stdout=stdout, stderr=subprocess.DEVNULL, timeout=tout,
                           preexec_fn=limits).returncode
    except subprocess.TimeoutExpired:
        return None, float(tout)
    return r, time.time() - t


def stats(f):
    v = c = l = 0
    try:
        for line in open(f):
            if line[:1] in "cae":
                continue
            if line[:1] == "p":
                v = int(line.split()[2])
                continue
            n = len(line.split()) - 1
            if n >= 0:
                c += 1
                l += n
    except Exception:
        return "?", "?", "?"
    return v, c, l


def done():
    d = {}
    if os.path.exists(RES):
        for l in open(RES):
            x = l.rstrip("\n").split("\t")
            d[(x[0], x[1], x[2], x[3])] = x[4:]
    return d


def record(*x):
    with open(RES, "a") as f:
        f.write("\t".join(str(y) for y in x) + "\n")


def do_pre(name, cmd):
    d = done()
    os.makedirs(os.path.join(W, name), exist_ok=True)

    def one(row):
        b = base(row[2])
        if ("pre", name, "", b) in d:
            return
        inp = plain(row[2])
        out = os.path.join(W, name, b)
        if "%o" in cmd:
            r, t = run([inp if x == "%i" else out if x == "%o" else x for x in cmd.split()], PRETOUT)
        else:
            with open(out, "w") as f:
                r, t = run([inp if x == "%i" else x for x in cmd.split()], PRETOUT, f)
        v = VERDICT.get(r, "" if r == 0 else "TO" if r is None else "ERR%d" % r)
        st = stats(out) if r == 0 else ("", "", "")
        record("pre", name, "", b, v, "%.2f" % t, *st)
        print(name, b, v, "%.2f" % t, *st, flush=True)
    with ThreadPoolExecutor(JOBS) as p:
        list(p.map(one, sample()))


def do_solve(pre, name, cmd):
    d = done()
    if pre == "none":
        for row in sample():
            b = base(row[2])
            plain(row[2])
            if ("pre", "none", "", b) not in d:
                record("pre", "none", "", b, "", "0.00", *stats(os.path.join(W, "none", b)))
        d = done()

    def one(row):
        b = base(row[2])
        if ("solve", pre, name, b) in d:
            return
        p = d.get(("pre", pre, "", b))
        if p is None or p[0] != "":
            return
        inp = os.path.join(W, pre, b)
        r, t = run([inp if x == "%i" else x for x in cmd.split()], TOUT)
        v = VERDICT.get(r, "TO" if r is None else "ERR%d" % r)
        record("solve", pre, name, b, v, "%.2f" % t)
        print(pre, name, b, v, "%.2f" % t, flush=True)
    with ThreadPoolExecutor(JOBS) as p:
        list(p.map(one, sample()))


def report():
    d = done()
    rows = sample()
    pres = sorted({k[1] for k in d if k[0] == "pre"}, key=lambda x: (x != "none", x))
    solvers = sorted({k[2] for k in d if k[0] == "solve"})
    truth = {}
    for k, v in d.items():
        if v[0] in "TF" and v[0]:
            truth.setdefault(k[3], set()).add(v[0])
    bad = [b for b, s in truth.items() if len(s) > 1]
    print("files: %d   with a verdict from anyone: %d   verdict mismatches: %s" % (len(rows), len(truth), bad))
    print("\n%-22s %6s %6s %6s %9s %9s" % ("preprocessor", "solved", "TO", "ERR", "pre time", "lits out"))
    for p in pres:
        vs = [d.get(("pre", p, "", base(r[2]))) for r in rows]
        vs = [v for v in vs if v]
        lits = sum(int(v[4]) for v in vs if v[0] == "" and v[4] not in ("", "?"))
        print("%-22s %6d %6d %6d %9.1f %9d" % (p, sum(v[0] in ("T", "F") for v in vs), sum(v[0] == "TO" for v in vs),
              sum(v[0].startswith("ERR") for v in vs), sum(float(v[1]) for v in vs), lits))
    print("\nsolved (pre verdict counts as solved); PAR2 with pre time included, limit %d" % TOUT)
    print("%-22s" % "" + "".join("%16s" % s for s in solvers))
    for p in pres:
        line = "%-22s" % p
        for s in solvers:
            n = 0
            par = 0.0
            seen = 0
            for r in rows:
                b = base(r[2])
                pv = d.get(("pre", p, "", b))
                if pv is None:
                    continue
                if pv[0] in ("T", "F"):
                    n += 1
                    par += float(pv[1])
                    seen += 1
                    continue
                sv = d.get(("solve", p, s, b))
                if pv[0] != "":
                    par += 2 * TOUT
                    seen += 1
                    continue
                if sv is None:
                    continue
                seen += 1
                if sv[0] in ("T", "F"):
                    n += 1
                    par += float(pv[1]) + float(sv[1])
                else:
                    par += 2 * TOUT
            line += "%16s" % ("%d/%d %.0f" % (n, seen, par) if seen else "-")
        print(line)


if __name__ == "__main__":
    if sys.argv[1] == "pre":
        do_pre(sys.argv[2], sys.argv[3])
    elif sys.argv[1] == "solve":
        do_solve(sys.argv[2], sys.argv[3], sys.argv[4])
    else:
        report()
