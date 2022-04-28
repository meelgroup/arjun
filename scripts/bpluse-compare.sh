#!/bin/bash

# /usr/bin/time --verbose ./B+E_linux -limSolver=500 -B=x  $1 > out 2> out2
# grep "input variables computed" out
# grep "User time" out2 | sed "s/\t//g"
echo "Running on CNF file $1"

fname="$1-noind"
grep -v "c ind" $1 > $fname
/usr/bin/time --verbose ./BiPe -preproc "$fname" > "$fname-simplified"
./count_literals.py "$fname-simplified"

