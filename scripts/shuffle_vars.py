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
import random

if len(sys.argv) != 4:
    print("ERROR: You need a seed and exactly two filenames, input + outpt")
    exit(-1)

random.seed(int(sys.argv[1]))

# read set lits
num_vars = None
num_cls = None
cls = []
with open(sys.argv[2], "r") as f:
    for line in f:
        l = line.strip()
        if len(line) < 1:
            continue

        if line[0] == "c":
            continue

        if line[0] == "p":
            line = line.split()
            num_vars = int(line[2])
            num_cls = int(line[3])
            continue

        assert num_vars is not None
        assert num_cls is not None
        l = l.split()
        cl = []
        #print(l)
        for lit in l:
            lit = int(lit)
            if lit == 0: break
            if abs(lit) > num_vars:
                print("Error! Lit %s in CNF but num vars promised to be: %s" % (lit, num_vars))
                exit(-1)
            cl.append(lit)
        cls.append(cl)

assert num_vars is not None, "no header!"
assert num_cls is not None
assert num_cls == len(cls), "Header is wrong!"

mymap_list = []
for i in range(1, num_vars+1):
    mymap_list.append(i)

random.shuffle(mymap_list)

mymap = {}
for i in range(1, num_vars+1):
    mymap[i] = mymap_list[i-1]

random.shuffle(cls)

with open(sys.argv[3], "w") as f:
    f.write("p cnf %d %d\n" %(num_vars, num_cls))
    for cl in cls:
        for l in cl:
            l2 = mymap[abs(l)]
            if l < 0: l2 = -l2
            f.write("%d " % l2)
        f.write("0\n");

print("Done")
