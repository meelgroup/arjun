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
./arjun $B --compindep 0 --oraclevivif 0 --unsatdefine 1 "$A" out > arjun_out
retval=$?
if [ $retval -ne 0 ]; then
    echo "Error: arjun failed"
    tail arjun_out
    exit -1
fi
echo "New count of $A:"
./count_literals.py out

echo "Doing UNSAT based synthesis"
./arjun $B --compindep 0 --oraclevivif 0 --oraclesparsify 0 --renumber 0 --unsatdefine 1 --iter1 0 --iter2 0 out out2 > arjun_out2
retval=$?
if [ $retval -ne 0 ]; then
    echo "Error: arjun UNSAT failed"
    tail arjun_out2
    exit -1
fi

grep "final extension" arjun_out2
