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
set_lits = {}
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
            set_lits[abs(int(l[0]))] = 1
            continue

        num_cls +=1
        for x in l:
            if x != "0":
                num_lits+=1
    

print("num set lits: ", len(set_lits))
print("num (non-set) vars: ", num_vars-len(set_lits))
print("num (non-unit) cls: ", num_cls)
print("num (non-unit) lits: ", num_lits)
