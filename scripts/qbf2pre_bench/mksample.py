#!/usr/bin/env python3
# Stratified sample of forall-exists files under ~/media/qbf: per family, files evenly spread over
# size. Prints sample.tsv: set, family, path.
import os, re, sys, math, collections
sys.path.insert(0, os.path.expanduser("~/media/qbf/qbflib"))
import qbf_prefix
R = os.path.expanduser("~/media/qbf")

def is_ae(p):
    try:
        return qbf_prefix.file_blocks(p) == ["a", "e"]
    except Exception:
        return False

def pick(files, k):
    files = sorted(files, key=lambda f: (os.path.getsize(f), f))
    if len(files) <= k:
        return files
    return [files[int((i + 0.5) * len(files) / k)] for i in range(k)]

def fam(name):
    return re.split(r"[-_.0-9]", name)[0]

out = []
seenfam = set()
def by_family(d, tag, k_of, check=False):
    fams = collections.defaultdict(list)
    for f in sorted(os.listdir(d)):
        if "qdimacs" not in f: continue
        p = os.path.join(d, f)
        if check and not is_ae(p): continue
        fams[fam(f)].append(p)
    for name in sorted(fams):
        if tag == "eval20-pcnf" and name in seenfam: continue
        seenfam.add(name)
        for p in pick(fams[name], k_of(len(fams[name]))):
            out.append((tag, name, p))

k = lambda n: 1 if n < 9 else 2 if n < 60 else 3
by_family(R + "/qbfeval17/2QBF", "eval17-2qbf", k)
by_family(R + "/qbfeval20/PCNF", "eval20-pcnf", lambda n: 1, check=True)
by_family(R + "/2qbf/2010-comp", "2010", lambda n: 1 if n < 30 else 2)
tac = 0
for d in sorted(os.listdir(R + "/qbflib")):
    dd = os.path.join(R, "qbflib", d)
    if not os.path.isdir(dd): continue
    if "Tacchella" in d:
        if "2qbf" not in d: continue
        tac += 1
        if tac % 5 != 1: continue
    fs = [os.path.join(dd, f) for f in sorted(os.listdir(dd)) if "qdimacs" in f]
    fs = [f for f in fs if is_ae(f)]
    for p in pick(fs, 1): out.append(("qbflib", d, p))
rb = R + "/abdst-paper/robots2d"
for p in pick([os.path.join(rb, f) for f in os.listdir(rb) if "qdimacs" in f], 3):
    out.append(("robots2d", "robots2d", p))
seen = set()
for tag, name, p in out:
    if p in seen: continue
    seen.add(p)
    print(tag, name, p, sep="\t")
