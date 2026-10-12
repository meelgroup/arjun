#!/usr/bin/env python3
# Reflexive resolution-path dependency scheme on forall-exists QDIMACS: how many universal
# literal occurrences would dependency-based forall reduction remove (pedant's --rrs --forall-reduction)?
# Samples at most MAXU universals per file. Usage: rrs.py FILE...
import sys, random, time
MAXU = 60
def parse(fn):
    univ = set(); cls = []
    for line in open(fn):
        t = line.split()
        if not t or t[0] in "cp": continue
        if t[0] == "a": univ.update(int(x) for x in t[1:-1]); continue
        if t[0] == "e": continue
        c = [int(x) for x in t[:-1]]
        if c: cls.append(c)
    return univ, cls
def reach(start, cls, occ, univ):
    # literals p such that a resolution path from `start` ends in a clause holding p (p not the entry literal)
    reached = set(); entry = {}; todo = []
    def enter(ci, via):
        if ci not in entry:
            entry[ci] = via
            for q in cls[ci]:
                if q != via and q not in reached:
                    reached.add(q); todo.append(q)
        elif entry[ci] is not None and entry[ci] != via:
            q = entry[ci]; entry[ci] = None
            if q not in reached:
                reached.add(q); todo.append(q)
    for ci in occ.get(start, ()): enter(ci, start)
    while todo:
        p = todo.pop()
        if abs(p) in univ: continue
        for ci in occ.get(-p, ()): enter(ci, -p)
    return reached
for fn in sys.argv[1:]:
    t0 = time.time()
    univ, cls = parse(fn)
    if not cls or not univ:
        continue
    if sum(map(len, cls)) > 400000:
        print(fn.split("/")[-1], "skipped: too big"); continue
    occ = {}
    for i, c in enumerate(cls):
        for l in c: occ.setdefault(l, []).append(i)
    exist = {abs(l) for c in cls for l in c} - univ
    us = sorted(u for u in univ if u in occ or -u in occ)
    random.seed(1); samp = us if len(us) <= MAXU else random.sample(us, MAXU)
    tot = rem = 0; depfrac = 0.0; nodep = None
    for u in samp:
        rp = reach(u, cls, occ, univ); rn = reach(-u, cls, occ, univ)
        dep = {e for e in exist if (e in rp and -e in rn) or (-e in rp and e in rn)}
        depfrac += len(dep) / max(1, len(exist))
        nodep = (exist - dep) if nodep is None else nodep - dep
        for l in (u, -u):
            for ci in occ.get(l, ()):
                tot += 1
                if not any(abs(q) in dep for q in cls[ci]): rem += 1
    print("%s univ=%d(sampled %d) exist=%d univ-lit-occs=%d removable=%d (%.1f%%) avg-dep-frac=%.2f exist-indep-of-all-sampled=%d T=%.1f" % (
        fn.split("/")[-1], len(us), len(samp), len(exist), tot, rem, 100.0 * rem / max(1, tot), depfrac / max(1, len(samp)),
        len(nodep or ()), time.time() - t0), flush=True)
