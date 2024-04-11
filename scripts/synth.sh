#!/usr/bin/bash
set +x

# ./arjun wage_circuit_div.t1.i18.777adaa9.stp.cnf out rec
# ~/development/sat_solvers/cadical/build/cadical out > sol
# ./solextend rec sol --verb 1
A="$1"
shift
B="$@"
echo "opts: $B"
rm -f proof*
rm -f core*

echo "Orig count of $A:"
./count_literals.py "$A"

echo "Doing BVE based synthesis"
./arjun $B --comp 0 "$A" --oraclevivif 0 out --simp 1 --probe 1 --renumber 1 > arjun_out
echo "New count of $A:"
./count_literals.py out

echo "Doing UNSAT based synthesis"
./arjun $B --comp 0 out out2 --oraclevivif 0 --oraclespars 0 --renumber 0 --synthdefine 1 --iter1 0 --iter2 0 > arjun_out2
grep "final extension" arjun_out2
