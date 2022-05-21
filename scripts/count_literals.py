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
set_vals = {}

# read set lits
with open(sys.argv[1], "r") as f:
    for line in f:
        l = line.strip()
        if len(line) < 1:
            continue

        if line[0] == "c":
            continue

        if line[0] == "p":
            line = line.split()
            print(line)
            num_vars = int(line[2])
            continue

        l = l.split()
        #print(l)
        if len(l) == 2:
            lit = int(l[0])
            set_vals[abs(lit)] = lit > 0
            continue

with open(sys.argv[1], "r") as f:
    for line in f:
        l = line.strip()
        if len(line) < 1:
            continue
    
        if line[0] == "c":
            continue
    
        if line[0] == "p":
            line = line.split()
            print(line)
            num_vars = int(line[2])
            continue
    
        l = l.split()
        if len(l) == 2:
            lit = int(l[0])
            set_vals[abs(lit)] = lit > 0
            continue

        sat_cl = False
        l2 = []
        for lit in l:
            lit = int(lit)
            if abs(lit) in set_vals:
                val = set_vals[abs(lit)]
                if lit < 0: val ^= True
                if val: sat_cl = True
            else:
                l2.append(lit)

        if sat_cl:
            continue

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
    

print("num set lits        ", len(set_vals))
print("num (non-set) vars  ", num_vars-len(set_vals))
print("num cls             ", num_cls)
print("num bin cls         ", num_bin_cls)
print("max cl size         ", max_cl_sz)
if (non_bin_cls != 0): print("avg non-bin cl sz    %-4.1f" % (float(tot_non_bin_cl_size)/float(non_bin_cls)))
else: print("avg non-bin cl sz   %-4.1f (no non-bin cl)" % 0)
print("num (non-unit) lits ", num_lits)
