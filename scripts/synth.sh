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

echo "File $A"
./count_literals.py "$A" > orig
cat orig
cnt_old=$(cat orig | grep outp | awk '{print $4}')
echo "-----------------"

timeout 10 /usr/bin/time --verbose ./arjun $B --synth "$A" out > arjun_out 2>&1
retval=$?
if [ $retval -ne 0 ]; then
    echo "Error: arjun failed, check arjun_out"
    # tail arjun_out
    exit 255
fi

num_core=$(find core* | wc -l)
num_proof=$(find proof* | wc -l)
proof_lines=$(cat proof* | wc -l)
core_lines=$(cat core* | wc -l)
cnt=$(./count_literals.py out | grep outp | awk '{print $4}')

# echo "Num core files   : $num_core"
# echo "Num proof files  : $num_proof"
# echo "Core lines total : $core_lines"
# echo "Proof lines total: $proof_lines"

echo "-----------------"
padoa=$(grep -i "defined via Padoa" arjun_out | awk '{print $5}')
t=$(grep -i "User time" arjun_out | awk '{print $4}')
bve=$(python -c "print ($cnt_old-$cnt-$padoa)")
echo "Old count             : $cnt_old"
echo "Padoa                 : $padoa"
echo "BVE, replace, backbone: $bve"
echo "New count             : $cnt"
echo "Time                  : $t"
