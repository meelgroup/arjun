#!/bin/bash

# /usr/bin/time --verbose ./B+E_linux -limSolver=500 -B=x  $1 > out 2> out2
# grep "input variables computed" out
# grep "User time" out2 | sed "s/\t//g"
#
# good example files:
# faster_with_be/wage_circuit_div.t1.i18.777adaa9.stp.cnf
# faster_with_be/amm-hhk2008-2.c.stp.cnf
# ProcessBean.cnf
# pollard.cnf
# track1_116.mcc2020_cnf
# blasted_TR_b14_even3_linear.cnf.gz.no_w.cnf

echo "Running on CNF file $1"

fname="$1-noind"
grep -v "c ind" "$1" > "$fname"
echo "Running Arjun..."
# config=""
# config="--gates 1 --empty 1 --irreggate 0"
/usr/bin/time ./arjun "$2" "$3" "$4" "$5" "$fname" "$fname-simplified-arjun" > "${fname}-arjun-output"

./count_literals.py "$fname-simplified-arjun" >"${fname}_count_arj_out"

echo "Running BPE (new, compiled)"
/usr/bin/time ./BiPe -preproc "$fname" > "$fname-simplified-bpe"
./count_literals.py "$fname-simplified-bpe" > "${fname}_count_bpe_out"

echo "ARJUN vs BPE (new, compiled)"
paste "${fname}_count_arj_out" "${fname}_count_bpe_out"

