#!/bin/bash
cleanfile=$(mktemp)
solfile=$(mktemp)
normalized=$(mktemp)
input=$1
mytime=1000
mytime2=1000

echo "------------------------------------------------------------------"
echo "Doing file $1...."
sed "s/p show/ind/" $1 > $normalized
echo "Running Arjun on $1"
./doalarm $mytime ./arjun $normalized  --elimtofile $cleanfile
found=`grep "^p cnf" $cleanfile`
if [[ $found == *"p cnf"* ]]; then
   echo "c o OK, Arjun succeeded"
   multi=`grep "^c MUST MUTIPLY BY" $cleanfile| sed "s/2\*\*//" | awk '{print $5}'`
   echo "running ganak on simplified file..."
   ./doalarm $mytime /home/soos/development/sat_solvers/ganak/build/ganak -cs 4000 -t $mytime $cleanfile > $solfile
   solved_by_ganak=`grep "solutions" $solfile`
   if [[ $solved_by_ganak == *"solutions"* ]]; then
        count=`grep "^s .*mc" $solfile | awk '{print $3}'`
        export BC_LINE_LENGTH=99999000000
        if [[ "$count" == "0" ]]; then
            count=$count
        else
            count=`echo "$count*(2^$multi)" | bc -l`
        fi
        echo "count with preproc: $count"
    fi
#     echo "Running CMS on simplified file..."
#     rm -f out_simp_sols
#     ../../cryptominisat/build/cryptominisat5 --maxsol 200000 --verb 0 --onlysampling $cleanfile > out_simp_sols
#     count_cms_simp=`grep "^v" out_simp_sols  | wc -l`
#     echo "count by CMS simp: $count_cms_simp"
fi

# echo "*****************"
# echo "Running CMS on orig file..."
# rm -f out_orig_sols
# ../../cryptominisat/build/cryptominisat5 --maxsol 200000 --verb 0 --onlysampling $cleanfile > out_orig_sols
# count_cms_orig=`grep "^v" out_orig_sols  | wc -l`
# echo "count by CMS orig: $count_cms_orig"
# echo "CMS   count w/ arjun: $count_cms_simp -- without arjun: $count_cms_orig"
# exit 0

echo "Now running ganak plainly on $1..."
./doalarm $mytime2 /home/soos/development/sat_solvers/ganak/build/ganak -cs 4000 -t $mytime2 $normalized > $solfile
solved_by_ganak=`grep "solutions" $solfile`
if [[ $solved_by_ganak == *"solutions"* ]]; then
    count2=`grep "^s .*mc" $solfile | awk '{print $3}'`
    echo "count without preproc: $count2"

    echo "ARJUN count w/ arjun: $count -- without arjun: $count2"
    if [[ $count != $count2 ]]; then
        echo "ERRRRROOOOORRR"
    else
        echo "OK"
    fi
fi

rm -f $normalized
rm -f $solfile
#rm -f $cleanfile
