#!/usr/bin/env python3
# chain.py FIRST NAME 'cmd %i': a second preprocessor (writing to stdout) on the outputs of
# preprocessor FIRST of bench.py, recorded as preprocessor "FIRST+NAME"
import os, sys, subprocess, time
sys.argv, first, name, cmd = sys.argv[:1], sys.argv[1], sys.argv[2], sys.argv[3]
import bench
d = bench.done(); pre = first + "+" + name
os.makedirs(os.path.join(bench.W, pre), exist_ok=True)
for row in bench.sample():
    b = bench.base(row[2])
    a = d.get(("pre", first, "", b))
    if a is None or ("pre", pre, "", b) in d: continue
    if a[0] != "":
        bench.record("pre", pre, "", b, *a); continue
    inp = os.path.join(bench.W, first, b); out = os.path.join(bench.W, pre, b)
    with open(out, "w") as f:
        r, t = bench.run([inp if x == "%i" else x for x in cmd.split()], 120, f)
    st = bench.stats(out)
    v = bench.VERDICT.get(r, "" if r == 0 else "TO" if r is None else "ERR%d" % r)
    bench.record("pre", pre, "", b, v, "%.2f" % (float(a[1]) + t), *(st if v == "" else ("", "", "")))
    print(pre, b, v, "%.2f" % t, *st, flush=True)
