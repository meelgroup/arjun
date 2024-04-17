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

num_core=$(find core* | wc -l)
num_proof=$(find proof* | wc -l)
proof_lines=$(cat proof* | wc -l)
core_lines=$(cat core* | wc -l)
cnt=$(./count_literals.py out | grep outp | awk '{print $4}')

echo "New count: $cnt"
echo "Num core files   : $num_core"
echo "Num proof files  : $num_proof"


echo "Core lines total : $core_lines"
echo "Proof lines total: $proof_lines"

