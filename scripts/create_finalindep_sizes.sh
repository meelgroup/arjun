#!/bin/bash

module unload gcc/4.9.3
module load anaconda/3
module load openmpi/intel/1.10.2
for x in `ls | grep $1`; do
    (cd $x
    echo At $x
    pwd
    xzgrep " 0$" *.out_finalindep.xz | awk '{print $1 " " NF-3}' | sed "s/.cnf.gz.no_w.cnf.gz.out_finalindep.xz:c/.cnf.gz/" > final_indeps.csv
    grep -f unsolved_pre.csv /home/projects/11000744/matesoos/counting2-vars.csv >> final_indeps.csv
    cat final_indeps.csv | awk '{a+=$2;x+=1} END{printf "%7.3f", a/x}' > final_indeps_avg.csv
    );
done
