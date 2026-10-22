#!/usr/bin/env python3
# Fuzzes arjun --coverdrop: the (weighted) projected count must not change. From build/:
#   ./fuzz_cover_drop.py [--num N] [--seed S] [--ganak PATH] [--arjun PATH]

import argparse
import os
import random
import re
import stat
import subprocess
import sys
from fractions import Fraction


def unique_file(fname_begin, fname_end=".cnf", max_num_files=2700):
    for counter in range(1, max_num_files + 1):
        fname = "out/" + fname_begin + '_' + str(counter) + fname_end
        try:
            fd = os.open(fname, os.O_CREAT | os.O_EXCL, stat.S_IREAD | stat.S_IWRITE)
            os.fdopen(fd).close()
            return fname
        except OSError:
            pass
    print("Cannot create unique_file %s_*%s in out/" % (fname_begin, fname_end))
    sys.exit(-1)


def rand_lit(v):
    return v if random.random() < 0.5 else -v


# psi over the sampling vars X, then components over their own ys and a few
# X each, of kinds that end up dropped, replaced by cubes, or kept. Dense
# enough that BVE does not eliminate them before coverdrop sees them
def gen_cnf(weighted):
    nx = random.randint(3, 12)
    xs = list(range(1, nx + 1))
    nvars = nx
    cls = []
    for _ in range(random.choice([0, 0, 1, 2, 4])):
        cls.append([rand_lit(v) for v in random.sample(xs, min(nx, random.randint(1, 3)))])
    comps = []
    for _ in range(random.randint(1, 6)):
        ys = list(range(nvars + 1, nvars + 1 + random.randint(3, 14)))
        nvars += len(ys)
        cx = random.sample(xs, random.randint(1, min(4, nx)))
        kind = random.choice(["easy", "tight", "def", "rand"])
        ratio = {"easy": 2.0, "tight": 4.0, "def": 2.5, "rand": random.uniform(1, 5)}[kind]
        for _ in range(max(1, int(len(ys) * ratio))):
            vs = random.sample(ys + cx, min(len(ys + cx), random.choice([2, 3, 3, 3, 4])))
            if not any(v in ys for v in vs):
                vs[0] = random.choice(ys)
            cls.append([rand_lit(v) for v in vs])
        if kind == "def" and len(ys) > 1:
            y, a, b = ys[0], rand_lit(random.choice(cx + ys[1:])), rand_lit(random.choice(cx + ys[1:]))
            cls += [[-y, a], [-y, b], [y, -a, -b]]
        comps.append(ys)
    # sometimes two components share a y
    if len(comps) > 1 and random.random() < 0.2:
        a, b = random.sample(comps, 2)
        cls.append([rand_lit(random.choice(a)), rand_lit(random.choice(b))])

    lines = ["c t pwmc" if weighted else "c t pmc", "p cnf %d %d" % (nvars, len(cls))]
    lines += [" ".join(map(str, cl)) + " 0" for cl in cls]
    lines.append("c p show " + " ".join(map(str, xs)) + " 0")
    if weighted:
        for v in range(1, nvars + 1):
            if random.random() < 0.3:
                w = Fraction(random.randint(1, 7), 8)
                lines.append("c p weight %d %s 0" % (v, w))
                lines.append("c p weight %d %s 0" % (-v, 1 - w))
    return "\n".join(lines) + "\n"


def run(cmd, timeout):
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        return p.returncode, p.stdout + p.stderr
    except subprocess.TimeoutExpired:
        return None, ""


def count(ganak, fname, weighted, timeout):
    cmd = [ganak, "--verb", "0", "--arjun", "0"] + (["--mode", "1"] if weighted else []) + [fname]
    rc, out = run(cmd, timeout)
    if rc is None:
        return None
    m = re.search(r"^c s exact arb (?:int|frac) (\S+)", out, re.M)
    if not m:
        if re.search(r"^s UNSATISFIABLE", out, re.M):
            return Fraction(0)
        print("ERROR: no count from ganak on %s:\n%s" % (fname, out[-2000:]))
        sys.exit(-1)
    return Fraction(m.group(1))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--num", type=int, default=100)
    parser.add_argument("--seed", type=int, default=None)
    parser.add_argument("--ganak", default="../../ganak/build/ganak")
    parser.add_argument("--arjun", default="./arjun")
    parser.add_argument("--timeout", type=int, default=30)
    opts = parser.parse_args()
    seed = opts.seed if opts.seed is not None else random.SystemRandom().randint(0, 2**63)
    random.seed(seed)
    print("Seed: %d" % seed)
    os.makedirs("out", exist_ok=True)

    stats = {"done": 0, "skipped": 0, "dropped": 0, "replaced": 0}
    for i in range(opts.num):
        weighted = random.random() < 0.3
        fname = unique_file("coverdrop")
        out_fname = fname + "-out.cnf"
        with open(fname, "w") as f:
            f.write(gen_cnf(weighted))
        cmd = [opts.arjun, "--verb", "1",
               "--coverdrop", str(random.choice([0.001, 0.01, 0.1, 1, 100])),
               "--coverdropcubes", str(random.choice([0, 1, 3, 50, 1000])),
               "--coverdropw", str(random.randint(0, 1)),
               "--sbva", str(random.choice([0, 1])),
               "--bve", str(random.choice([0, 0, 1])),
               "--bveresolvmaxsz", str(random.choice([2, 4, 12])),
               "--probe", str(random.randint(0, 1))] + (["--mode", "1"] if weighted else []) + [fname, out_fname]
        rc, out = run(cmd, opts.timeout)
        if rc is None:
            stats["skipped"] += 1
            os.unlink(fname)
            continue
        if rc != 0:
            print("ERROR: arjun exited with %d\n%s\nREPRODUCE with: %s" % (rc, out[-3000:], " ".join(cmd)))
            sys.exit(-1)
        m = re.search(r"\[cover-drop\] components: \d+ tried: \d+ dropped: (\d+) replaced: (\d+)", out)
        if m:
            stats["dropped"] += int(m.group(1))
            stats["replaced"] += int(m.group(2))

        before = count(opts.ganak, fname, weighted, opts.timeout)
        after = count(opts.ganak, out_fname, weighted, opts.timeout)
        if before is None or after is None:
            stats["skipped"] += 1
        elif before != after:
            print("BUG: count %s before, %s after\nREPRODUCE with: %s" % (before, after, " ".join(cmd)))
            print("Seed: %d iteration: %d" % (seed, i))
            sys.exit(-1)
        else:
            stats["done"] += 1
        os.unlink(fname)
        os.unlink(out_fname)
        if (i + 1) % 20 == 0:
            print("Iterations: %d checked: %d skipped: %d components dropped: %d replaced: %d"
                  % (i + 1, stats["done"], stats["skipped"], stats["dropped"], stats["replaced"]), flush=True)
    print("All OK. checked: %d skipped: %d components dropped: %d replaced: %d"
          % (stats["done"], stats["skipped"], stats["dropped"], stats["replaced"]))


if __name__ == "__main__":
    main()
