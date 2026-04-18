#!/usr/bin/env python3
# -*- coding: utf-8 -*-

# Copyright (C) 2009-2020 Mate Soos
#
# This program is free software; you can redistribute it and/or
# modify it under the terms of the GNU General Public License
# as published by the Free Software Foundation; version 2
# of the License.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program; if not, write to the Free Software
# Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
# 02110-1301, USA.

import sys
from collections import Counter


def count_indep(tokens):
    # tokens are the vars in "c p show ..." / "c p optshow ..." lines,
    # terminated by a closing 0 which must not be counted.
    vars_ = [t for t in tokens if t != "0"]
    return len(vars_)


def percentile(sorted_vals, p):
    if not sorted_vals:
        return 0
    k = (len(sorted_vals) - 1) * (p / 100.0)
    f = int(k)
    c = min(f + 1, len(sorted_vals) - 1)
    if f == c:
        return sorted_vals[f]
    return sorted_vals[f] + (sorted_vals[c] - sorted_vals[f]) * (k - f)


def histogram(counter, label, max_bucket=10):
    # counter: {size -> count}, prints a simple histogram up to max_bucket,
    # then a single ">max_bucket" bucket for the rest.
    total = sum(counter.values())
    if total == 0:
        return
    print("%s distribution:" % label)
    max_count = max(counter.values())
    width = 40
    buckets = sorted(k for k in counter.keys() if k <= max_bucket)
    for k in buckets:
        v = counter[k]
        bar = "#" * max(1, int(v * width / max_count))
        print("  size %3d : %8d (%5.1f%%) %s" % (k, v, 100.0*v/total, bar))
    rest = sum(v for k, v in counter.items() if k > max_bucket)
    if rest > 0:
        bar = "#" * max(1, int(rest * width / max_count))
        print("  size >%2d : %8d (%5.1f%%) %s" % (max_bucket, rest, 100.0*rest/total, bar))


num_vars = 0
set_vals = {}
indep_size = None
opt_indep_size = None

# Pass 1: collect header, units, and indep declarations.
with open(sys.argv[1], "r") as f:
    for line in f:
        l = line.strip()
        if len(l) < 1:
            continue

        if l.startswith("c p show"):
            indep_size = count_indep(l.split()[3:])
            continue
        if l.startswith("c p optshow"):
            opt_indep_size = count_indep(l.split()[3:])
            continue
        if line[0] == "c":
            continue

        if line[0] == "p":
            parts = l.split()
            num_vars = int(parts[2])
            continue

        toks = l.split()
        if len(toks) == 2:
            lit = int(toks[0])
            set_vals[abs(lit)] = lit > 0
            continue

# Pass 2: clause statistics (with unit propagation applied).
num_cls = 0
num_lits = 0
num_bin_cls = 0
max_cl_sz = 0
tot_non_bin_cl_size = 0
non_bin_cls = 0
num_pos_lits = 0
num_neg_lits = 0
cl_size_hist = Counter()
var_occ = Counter()

with open(sys.argv[1], "r") as f:
    for line in f:
        l = line.strip()
        if len(l) < 1:
            continue
        if line[0] == "c" or line[0] == "p":
            continue

        toks = l.split()
        if len(toks) == 2:
            continue  # unit; already handled

        sat_cl = False
        l2 = []
        for tok in toks:
            lit = int(tok)
            if lit == 0:
                continue
            if abs(lit) in set_vals:
                val = set_vals[abs(lit)]
                if lit < 0:
                    val ^= True
                if val:
                    sat_cl = True
            else:
                l2.append(lit)

        if sat_cl:
            continue

        cl_len = len(l2)
        cl_size_hist[cl_len] += 1
        if cl_len == 2:
            num_bin_cls += 1
        else:
            tot_non_bin_cl_size += cl_len
            non_bin_cls += 1

        max_cl_sz = max(max_cl_sz, cl_len)
        num_cls += 1
        num_lits += cl_len
        for lit in l2:
            if lit > 0:
                num_pos_lits += 1
            else:
                num_neg_lits += 1
            var_occ[abs(lit)] += 1


print("num set lits         ", len(set_vals))
print("num (non-set) vars   ", num_vars - len(set_vals))
if indep_size is not None:
    print("indep size           ", indep_size)
else:
    print("indep size            (no 'c p show' line)")
if opt_indep_size is not None:
    print("opt indep size       ", opt_indep_size)
else:
    print("opt indep size        (no 'c p optshow' line)")
print("num long cls         ", num_cls - num_bin_cls)
print("num bin cls          ", num_bin_cls)
print("max cl size          ", max_cl_sz)
if non_bin_cls != 0:
    print("avg non-bin cl sz    %4.1f" % (float(tot_non_bin_cl_size) / float(non_bin_cls)))
else:
    print("avg non-bin cl sz    %4.1f (no non-bin cl)" % 0)
print("num (non-unit) lits  ", num_lits)

if num_lits > 0:
    print("")
    print("positive lits        %8d (%5.1f%%)" % (num_pos_lits, 100.0*num_pos_lits/num_lits))
    print("negative lits        %8d (%5.1f%%)" % (num_neg_lits, 100.0*num_neg_lits/num_lits))

if num_cls > 0:
    cl_sizes_sorted = sorted(cl_size_hist.elements())
    print("")
    print("clause size stats:")
    print("  min                %d" % cl_sizes_sorted[0])
    print("  max                %d" % cl_sizes_sorted[-1])
    print("  mean               %.2f" % (num_lits / num_cls))
    print("  p50                %.1f" % percentile(cl_sizes_sorted, 50))
    print("  p90                %.1f" % percentile(cl_sizes_sorted, 90))
    print("  p99                %.1f" % percentile(cl_sizes_sorted, 99))
    print("")
    histogram(cl_size_hist, "clause size")

if var_occ:
    occs_sorted = sorted(var_occ.values())
    n_active = len(var_occ)
    n_unused = (num_vars - len(set_vals)) - n_active
    total_occ = sum(occs_sorted)
    print("")
    print("variable occurrence stats (over %d variables with >=1 occurrence):" % n_active)
    print("  min                %d" % occs_sorted[0])
    print("  max                %d" % occs_sorted[-1])
    print("  mean               %.2f" % (total_occ / n_active))
    print("  p50                %.1f" % percentile(occs_sorted, 50))
    print("  p90                %.1f" % percentile(occs_sorted, 90))
    print("  p99                %.1f" % percentile(occs_sorted, 99))
    if n_unused > 0:
        print("  unused (non-set) vars %d" % n_unused)
    print("")
    occ_hist = Counter(var_occ.values())
    histogram(occ_hist, "variable occurrence count", max_bucket=10)
