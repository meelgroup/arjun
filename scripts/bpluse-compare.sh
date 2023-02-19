#!/bin/bash

# /usr/bin/time --verbose ./B+E_linux -limSolver=500 -B=x  $1 > out 2> out2
# grep "input variables computed" out
# grep "User time" out2 | sed "s/\t//g"
#
# good example files:
# faster_with_be/wage_circuit_div.t1.i18.777adaa9.stp.cnf
# faster_with_be/amm-hhk2008-2.c.stp.cnf
# ProcessBean
# pollard
# track1_116.mcc2020_cnf
# blasted_TR_b14_even3_linear.cnf.gz.no_w.cnf

echo "Running on CNF file $1"

fname="$1-noind"
grep -v "c ind" "$1" > "$fname"
echo "Running Arjun..."
config=""
/usr/bin/time ./arjun $config "$fname" "$fname-simplified-arjun" > /dev/null
./count_literals.py "$fname-simplified-arjun" > arj_out

echo "Running BPE (new, compiled)"
/usr/bin/time ./BiPe -preproc "$fname" > "$fname-simplified-bpe"
./count_literals.py "$fname-simplified-bpe" > bpe_out

echo "ARJUN vs BPE (new, compiled)"
paste arj_out bpe_out

