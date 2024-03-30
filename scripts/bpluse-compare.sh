#!/bin/bash

# /usr/bin/time --verbose ./B+E_linux -limSolver=500 -B=x  $1 > out 2> out2
# grep "input variables computed" out
# grep "User time" out2 | sed "s/\t//g"
#
# good example files:
# wage_circuit_div.t1.i18.777adaa9.stp.cnf
# amm-hhk2008-2.c.stp.cnf
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
stuff="${@:2}"

exec="./arjun --sbva 0 $stuff $fname $fname-simplified-arjun"
echo "Executing: $exec"
/usr/bin/time $exec > "${fname}-arjun-output" &

exec="./puura $stuff $fname $fname-simplified-puura"
echo "Executing: $exec"
/usr/bin/time $exec > "${fname}-puura-output" &

echo "Running BPE (new, compiled)"
/usr/bin/time ./BiPe -preproc "$fname" > "$fname-simplified-bpe" &

# echo "Running SSTD"
# /usr/bin/time ../../sharpsat-td/build/sharpSAT-prepro "$fname" > "$fname-simplified-sstd" &

wait
./count_literals.py "$fname-simplified-puura" >"${fname}_count_puura_out"
./count_literals.py "$fname-simplified-bpe" > "${fname}_count_bpe_out"
# ./count_literals.py "$fname-simplified-sstd" > "${fname}_count_sstd_out"
./count_literals.py "$fname-simplified-arjun" >"${fname}_count_arjun_out"

echo "ARJUN vs PUURA vs BPE (new, compiled) vs SSTD"
paste "${fname}_count_arjun_out" "${fname}_count_puura_out" "${fname}_count_bpe_out" "${fname}_count_sstd_out"

