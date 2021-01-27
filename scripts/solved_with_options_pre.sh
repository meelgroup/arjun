#!/bin/bash

check="$1"
FILE="20180321_110706599_p_cnf_320_1120.cnf"
FILE="001-80-12-sc2014.cnf"
FILE="01A-1.cnf.gz.no_w.cnf"
FILE="01A-1.cnf.gz.no_w.cnf"

rm out
for d in `ls | grep $check`; do
    echo $d;
    PAR2=`cat $d/PAR2score_pre`
    name=`xzgrep "Command being" $d/${FILE}.gz.timeout_pre.xz`
    numsolved=`wc -l $d/solved_pre.csv | awk '{print $1}'`
    numALL=`wc -l $d/allFiles_pre.csv  | awk '{print $1}'`
    revArj=`xzgrep -i "Arjun.*revision" $d/${FILE}.gz.out.xz | awk '{print $5}' | cut -c1-7`
    echo "$PAR2 $d $numsolved $numALL $revArj $name" >> out
done
sed "s/${FILE}.*//" out | sed "s/Command.*time.*approxmc//"  | sed "s/.solved.csv//" |                 sed "s/ *Command being timed.*approxmc//" | sed "s/\t/ /g" | sed "s/\t/ /g" | sort -n
