#!/usr/bin/bash
# set -x
# set -v

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
./arjun $B --synth "$A" out > arjun_out
retval=$?
if [ $retval -ne 0 ]; then
    echo "Error: arjun failed"
    tail arjun_out
    exit 255
fi
echo "New count of $A:"
./count_literals.py out | grep outp
