#!/usr/bin/env python
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


num_cls = 0
num_vars = 0
num_lits = 0
num_bin_cls = 0
max_cl_sz = 0
tot_non_bin_cl_size = 0
non_bin_cls = 0
set_vars = {}
input_vars = {}
opt_input_vars = {}

if len(sys.argv) < 2:
    print("ERROR: You need the filename")
    exit(-1)

verbose = False
if len(sys.argv) >= 3 and sys.argv[2].strip() == "-v":
    verbose = True

def remove_prefix(s, prefix):
    if s.startswith(prefix):
        return s[len(prefix):]
    else:
        return s

# read set lits
with open(sys.argv[1], "r") as f:
    for line in f:
        line = line.strip()
        if len(line) < 1:
            continue

        if line[0] == "c":
            if "c p show" in line:
                line = remove_prefix(line, "c p show")
                for var in line.split():
                    var = int(var)
                    if var != abs(var):
                        print("ERROR! c p show contains LITERAL not VARIABLE!")
                        exit(-1)
                    input_vars[var] = True
                    if var > num_vars:
                        print("Error! Var %s in 'c p show' but num vars promised to be: %s" % (var, num_vars))
                        exit(-1)
                continue
            if "c p optshow" in line:
                line = remove_prefix(line, "c p optshow")
                for var in line.split():
                    var = int(var)
                    if var != abs(var):
                        print("ERROR! c p show contains LITERAL not VARIABLE!")
                        exit(-1)
                    if var != 0:
                        opt_input_vars[var] = True
                    if var > num_vars:
                        print("Error! Var %s in 'c p show' but num vars promised to be: %s" % (var, num_vars))
                        exit(-1)
                continue

            # regular comment
            continue

        if line[0] == "p":
            line = line.split()
            if verbose: print(line)
            num_vars = int(line[2])
            continue

        line = line.split()
        for lit in line:
            if abs(int(lit)) > num_vars:
                print("Error! Lit %s in CNF but num vars promised to be: %s" % (lit, num_vars))
                exit(-1)

        # unit clause
        if len(line) == 2:
            lit = int(line[0])
            set_vars[abs(lit)] = lit > 0
            continue

seen_vars = {}
with open(sys.argv[1], "r") as f:
    for line in f:
        line = line.strip()
        if len(line) < 1:
            continue

        if line[0] == "c":
            continue

        if line[0] == "p":
            line = line.split()
            if verbose: print(line)
            num_vars = int(line[2])
            continue

        line = line.split()
        if len(line) == 2:
            lit = int(line[0])
            set_vars[abs(lit)] = lit > 0
            continue

        sat_cl = False
        l2 = []
        for lit in line:
            lit = int(lit)
            if abs(lit) in set_vars:
                val = set_vars[abs(lit)]
                if lit < 0: val ^= True
                if val: sat_cl = True
            else:
                l2.append(lit)

        if sat_cl:
            continue

        # fill seen
        for lit in line:
            lit = int(lit)
            seen_vars[abs(lit)] = True

        cl_len = len(l2)-1;
        if cl_len == 2:
            num_bin_cls += 1
        else:
            tot_non_bin_cl_size += cl_len
            non_bin_cls += 1

        max_cl_sz = max(max_cl_sz, cl_len)

        num_cls +=1
        for x in l2:
            if x != "0":
                num_lits+=1

num_output_not_set = 0
for i in range(1, num_vars+1):
    if (i not in input_vars) and (i not in set_vars) and (i in seen_vars):
        num_output_not_set += 1

if verbose:
    print("num set lits        ", len(set_vars))
print("num (non-set) vars       %7d" % (num_vars-len(set_vars)))
print("num input     vars       %7d" % (len(input_vars)))
print("num opt input vars       %7d" % (len(opt_input_vars)))
print("num outp      vars       %7d" % (num_output_not_set))
print("num cls                  %7d" % num_cls)
print("num bin cls              %7d" % num_bin_cls)
print("max cl size              %7d" % max_cl_sz)
if (non_bin_cls != 0):
    print("avg non-bin cl sz          %5.1f" % (float(tot_non_bin_cl_size)/float(non_bin_cls)))
else:
    print("avg non-bin cl sz           %5.1f (no non-bin cl)" % 0)
print("num (non-unit) lits      %7d" % num_lits)
