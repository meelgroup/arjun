#!/bin/bash
for i in {1..8}; do
    echo $i; a=$((i*25));
    echo "ulimit -t 5000" > todo-$i.sh;
    echo "ulimit -m 4000000" >> todo-$i.sh;
    head -n $a todo | tail -n 25 >> todo-$i.sh; chmod +x todo-$i.sh;
done

for i in {1..20}; do
    ./todo-$i.sh > out-$i 2>&1 &
done
wait
