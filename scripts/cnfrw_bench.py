#!/usr/bin/env python3
"""
A/B benchmark for arjun's CNF-rewrite (--cnfrw) module.

For every CNF and every config: run arjun (preprocess to a file), measure the
output CNF (vars / clauses / literals / binaries / long clauses), then count
the output with ganak (--arjun 0) and record count + time. Counts across
configs must agree; mismatches are flagged as ERROR.

Usage:
  scripts/cnfrw_bench.py [--configs "base:--cnfrw 0" "rw:--cnfrw 1"] \
      [--arjun-tout 300] [--ganak-tout 300] [--jobs 4] [--out results.csv] \
      [--arjun-extra "..."] [--ganak-extra "..."] files...

Run from anywhere; binaries default to <repo>/build/arjun and
<repo>/../ganak/build/ganak.
"""
import argparse
import concurrent.futures as cf
import csv
import gzip
import os
import re
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, ".."))


def cnf_stats(path):
    opener = gzip.open if path.endswith(".gz") else open
    nv = ncl = nlit = nbin = nlong = 0
    show = optshow = None
    with opener(path, "rt") as f:
        for line in f:
            if not line:
                continue
            c = line[0]
            if c == "p":
                nv = int(line.split()[2])
                continue
            if c == "c":
                if line.startswith("c p show"):
                    show = len(line.split()[3:-1])
                elif line.startswith("c p optshow"):
                    optshow = len(line.split()[3:-1])
                continue
            toks = line.split()
            if not toks:
                continue
            n = len(toks) - 1
            ncl += 1
            nlit += n
            if n == 2:
                nbin += 1
            elif n > 3:
                nlong += 1
    return dict(vars=nv, cls=ncl, lits=nlit, bin=nbin, long=nlong, show=show, optshow=optshow)


def run(cmd, tout):
    t = time.time()
    try:
        p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                           universal_newlines=True, timeout=tout)
        out, rc = p.stdout, p.returncode
    except subprocess.TimeoutExpired as e:
        out = (e.stdout.decode() if isinstance(e.stdout, bytes) else (e.stdout or "")) + "\nTIMEOUT\n"
        rc = -9
    return out, rc, time.time() - t


def parse_count(out):
    if "s UNSATISFIABLE" in out:
        return "0"
    for line in out.splitlines():
        line = line.strip()
        if line.startswith("s mc ") or line.startswith("s pmc "):
            return line.split()[2]
        if line.startswith("c s exact arb int "):
            return line.split()[5]
        if line.startswith("c s exact arb frac "):
            return line.split()[5]
        if "c s exact double prec-sci" in line:
            return line.split()[5]
        if line.startswith("c s exact arb float"):
            return line.split()[5]
    return None


def parse_cnfrw(out):
    d = {}
    for line in out.splitlines():
        if "[cnfrw] CNF vars" in line:
            m = re.search(r"vars (\d+) -> (\d+) cls (\d+) -> (\d+) lits (\d+) -> (\d+)", line)
            if m:
                d["rw_vars_in"], d["rw_vars_out"], d["rw_cls_in"], d["rw_cls_out"], \
                    d["rw_lits_in"], d["rw_lits_out"] = map(int, m.groups())
        if "[cnfrw] T detect" in line:
            m = re.search(r"total ([\d.]+)", line)
            if m:
                d["rw_time"] = float(m.group(1))
        if "[cnfrw] outputs" in line:
            m = re.search(r"outputs (\d+) removable (\d+) kept (\d+)", line)
            if m:
                d["rw_outputs"], d["rw_removable"], d["rw_kept"] = map(int, m.groups())
        if "[cnfrw] roots" in line:
            m = re.search(r"aig nodes (\d+) -> (\d+)", line)
            if m:
                d["rw_aig_before"], d["rw_aig_after"] = map(int, m.groups())
    return d


def permute_cnf(src, dst, seed):
    opener = gzip.open if src.endswith(".gz") else open
    with opener(src, "rt") as f:
        lines = f.read().splitlines()
    nv = 0
    for l in lines:
        if l.startswith("p cnf"):
            nv = int(l.split()[2])
            break
    perm = list(range(1, nv + 1))
    import random
    random.Random(seed).shuffle(perm)

    def m(tok):
        v = int(tok)
        if v == 0:
            return "0"
        return str(perm[abs(v) - 1] * (1 if v > 0 else -1))
    out = []
    for l in lines:
        if l.startswith("c p show") or l.startswith("c p optshow"):
            toks = l.split()
            out.append(" ".join(toks[:3]) + " " + " ".join(m(t) for t in toks[3:]))
        elif l.startswith("c p weight"):
            toks = l.split()
            out.append("c p weight " + m(toks[3]) + " " + " ".join(toks[4:]))
        elif l.startswith("p ") or l.startswith("c"):
            out.append(l)
        else:
            toks = l.split()
            if toks:
                out.append(" ".join(m(t) for t in toks))
    with open(dst, "w") as f:
        f.write("\n".join(out) + "\n")


def one(args, cnf, cname, cargs, perm=0):
    base = os.path.basename(cnf).replace(".cnf.gz", "").replace(".cnf", "")
    tag = f"{cname}" if perm == 0 else f"{cname}.p{perm}"
    outcnf = os.path.join(args.workdir, f"{base}.{tag}.cnf")
    incnf = cnf
    if perm != 0:
        incnf = os.path.join(args.workdir, f"{base}.perm{perm}.cnf")
        if not os.path.exists(incnf):
            permute_cnf(cnf, incnf, perm)
    arjun_cmd = [args.arjun, "--verb", "1"] + args.arjun_extra.split() + cargs.split() + [incnf, outcnf]
    aout, arc, at = run(arjun_cmd, args.arjun_tout)
    rec = dict(cnf=base, config=cname, perm=perm, arjun_rc=arc, arjun_t=round(at, 2))
    rec.update(parse_cnfrw(aout))
    with open(outcnf + ".arjun.log", "w") as f:
        f.write(aout)
    if arc != 0 or not os.path.exists(outcnf):
        rec["status"] = "arjun-fail" if arc != -9 else "arjun-tout"
        return rec
    rec.update(cnf_stats(outcnf))
    if args.ganak_tout > 0:
        ganak_cmd = [args.ganak, "--arjun", "0"] + args.ganak_extra.split() + [outcnf]
        gout, grc, gt = run(ganak_cmd, args.ganak_tout)
        with open(outcnf + ".ganak.log", "w") as f:
            f.write(gout)
        rec["ganak_t"] = round(gt, 2)
        cnt = parse_count(gout) if grc == 0 else None
        rec["count"] = cnt
        rec["status"] = "ok" if cnt is not None else ("ganak-tout" if grc == -9 else "ganak-fail")
    else:
        rec["status"] = "ok"
    if not args.keep:
        try:
            os.unlink(outcnf)
        except OSError:
            pass
    return rec


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("files", nargs="+")
    ap.add_argument("--configs", nargs="+", default=["base:--cnfrw 0", "rw:--cnfrw 1"],
                    help="name:args pairs")
    ap.add_argument("--arjun", default=os.path.join(REPO, "build", "arjun"))
    ap.add_argument("--ganak", default=os.path.join(REPO, "..", "ganak", "build", "ganak"))
    ap.add_argument("--arjun-extra", default="")
    ap.add_argument("--ganak-extra", default="")
    ap.add_argument("--arjun-tout", type=int, default=300)
    ap.add_argument("--ganak-tout", type=int, default=300, help="0 = do not count")
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--out", default="cnfrw_bench.csv")
    ap.add_argument("--workdir", default="/tmp/cnfrw_bench")
    ap.add_argument("--keep", action="store_true")
    ap.add_argument("--perms", type=int, default=1,
                    help="run each config on K variable renamings (perm 0 = original); summary uses medians")
    args = ap.parse_args()
    os.makedirs(args.workdir, exist_ok=True)
    configs = []
    for c in args.configs:
        name, _, a = c.partition(":")
        configs.append((name, a))

    jobs = [(cnf, n, a, p) for cnf in args.files for (n, a) in configs for p in range(args.perms)]
    results = []
    with cf.ThreadPoolExecutor(max_workers=args.jobs) as ex:
        futs = {ex.submit(one, args, cnf, n, a, p): (cnf, n, p) for (cnf, n, a, p) in jobs}
        for fut in cf.as_completed(futs):
            r = fut.result()
            results.append(r)
            print(f"{r['cnf']:<28} {r['config'] + ('' if r['perm'] == 0 else '.p%d' % r['perm']):<10} {r.get('status',''):<11} "
                  f"vars={r.get('vars','-'):<7} cls={r.get('cls','-'):<8} lits={r.get('lits','-'):<9} "
                  f"arjunT={r.get('arjun_t','-'):<7} ganakT={r.get('ganak_t','-'):<7} cnt={str(r.get('count','-'))[:20]}",
                  flush=True)

    # count agreement
    by_cnf = {}
    for r in results:
        by_cnf.setdefault(r["cnf"], []).append(r)
    errors = 0
    for cnf, rs in sorted(by_cnf.items()):
        cnts = set(str(r.get("count")) for r in rs if r.get("count") is not None)
        if len(cnts) > 1:
            errors += 1
            print(f"ERROR: count mismatch on {cnf}: " + ", ".join(f"{r['config']}={r.get('count')}" for r in rs))

    if args.perms > 1:
        import statistics
        print("\n=== per-instance medians over permutations (vars/cls/lits; ganakT median of solved) ===")
        for cnf, rs in sorted(by_cnf.items()):
            line = f"{cnf:<28}"
            for name, _ in configs:
                sel = [r for r in rs if r["config"] == name and "vars" in r]
                if not sel:
                    line += f" {name}: -"
                    continue
                med = lambda k: statistics.median(r[k] for r in sel)
                gt = [r["ganak_t"] for r in sel if r.get("status") == "ok" and "ganak_t" in r]
                line += (f" {name}: v={med('vars'):.0f}[{min(r['vars'] for r in sel)}-{max(r['vars'] for r in sel)}]"
                         f" c={med('cls'):.0f} l={med('lits'):.0f}"
                         + (f" gT={statistics.median(gt):.1f}" if gt else "") + f" ({len(sel)}/{args.perms})")
            print(line)

    keys = ["cnf", "config", "perm", "status", "vars", "cls", "lits", "bin", "long", "show", "optshow",
            "arjun_t", "ganak_t", "count", "rw_time", "rw_vars_in", "rw_vars_out", "rw_cls_in",
            "rw_cls_out", "rw_lits_in", "rw_lits_out", "rw_outputs", "rw_removable", "rw_kept",
            "rw_aig_before", "rw_aig_after", "arjun_rc"]
    with open(args.out, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=keys, extrasaction="ignore")
        w.writeheader()
        for r in sorted(results, key=lambda r: (r["cnf"], r["config"])):
            w.writerow(r)

    # summary per config vs first config (perm 0 runs only)
    base = configs[0][0]
    print("\n=== summary (perm 0; only instances where all configs finished arjun) ===")
    for name, _ in configs:
        tot = dict(vars=0, cls=0, lits=0, arjun_t=0.0, ganak_t=0.0, n=0, solved=0)
        for cnf, rs in by_cnf.items():
            d = {r["config"]: r for r in rs if r["perm"] == 0}
            if any(c not in d or "vars" not in d[c] for c, _ in configs):
                continue
            r = d[name]
            tot["n"] += 1
            for k in ("vars", "cls", "lits"):
                tot[k] += r[k]
            tot["arjun_t"] += r["arjun_t"]
            if r.get("status") == "ok" and r.get("count") is not None:
                tot["solved"] += 1
                tot["ganak_t"] += r.get("ganak_t", 0)
        print(f"{name:<10} n={tot['n']} vars={tot['vars']} cls={tot['cls']} lits={tot['lits']} "
              f"arjunT={tot['arjun_t']:.1f} solved={tot['solved']} ganakT(solved)={tot['ganak_t']:.1f}")
    if errors:
        print(f"\n{errors} COUNT MISMATCHES")
        sys.exit(1)


if __name__ == "__main__":
    main()
