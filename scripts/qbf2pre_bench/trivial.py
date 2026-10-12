#!/usr/bin/env python3
# Per file: trivial truth (drop universal literals -> SAT means one Y works for all X),
# plus cheap structure counts. Usage: trivial.py DIR_OF_PLAIN_QDIMACS
import os, subprocess, sys, tempfile
CAD = os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../cryptominisat/build/cryptominisat5")
d = sys.argv[1]
for b in sorted(os.listdir(d)):
    univ = set(); cls = []; nv = 0
    for line in open(os.path.join(d, b)):
        t = line.split()
        if not t or t[0] == "c": continue
        if t[0] == "p": nv = int(t[2]); continue
        if t[0] == "a": univ.update(int(x) for x in t[1:-1]); continue
        if t[0] == "e": continue
        cls.append([int(x) for x in t[:-1]])
    if not cls:
        print(b, "empty"); continue
    ex_only = sum(all(abs(l) not in univ for l in c) for c in cls)
    ex = [[l for l in c if abs(l) not in univ] for c in cls]
    # universal literals that are pure
    pos = {abs(l) for c in cls for l in c if l > 0 and abs(l) in univ}
    neg = {abs(l) for c in cls for l in c if l < 0 and abs(l) in univ}
    upure = len(pos ^ neg)
    with tempfile.NamedTemporaryFile("w", suffix=".cnf", delete=False) as f:
        f.write("p cnf %d %d\n" % (nv, len(ex)))
        for c in ex: f.write(" ".join(map(str, c)) + " 0\n")
    try:
        r = subprocess.run([CAD, "--verb", "0", "--maxtime", "10", f.name], stdout=subprocess.DEVNULL).returncode
    except Exception:
        r = -1
    os.unlink(f.name)
    print(b, "univ=%d cls=%d exonly=%d upure=%d trivtruth=%s" % (len(univ), len(cls), ex_only, upure, {10: "YES", 20: "no"}.get(r, "?")), flush=True)
