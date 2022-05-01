#!/bin/bash

# /usr/bin/time --verbose ./B+E_linux -limSolver=500 -B=x  $1 > out 2> out2
# grep "input variables computed" out
# grep "User time" out2 | sed "s/\t//g"
echo "Running on CNF file $1"

fname="$1-noind"
grep -v "c ind" $1 > $fname
/usr/bin/time ./arjun --elimtofile "$fname-simplified-arjun" "$fname" > /dev/null
./count_literals.py "$fname-simplified-arjun"

/usr/bin/time ./BiPe -preproc "$fname" > "$fname-simplified-bpe"
./count_literals.py "$fname-simplified-bpe"

