#!/bin/bash

a=(
# "amm-hhk2008-2.c.stp.cnf"
"blasted_TR_b14_even3_linear.cnf.gz.no_w.cnf"
"pollard.cnf"
"ProcessBean.cnf"
"wage_circuit_div.t1.i18.777adaa9.stp.cnf"
"mc2022_track1_115.cnf"
"mc2022_track1_037.cnf"
"mc2022_track1_079.cnf"
"mc2022_track1_105.cnf"
# "mc2022_track1_153.cnf" # checks backbone, really
)
for i in "${a[@]}"; do
    ./bpluse-compare.sh "$i"
done
