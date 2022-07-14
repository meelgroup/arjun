#!/bin/bash
for i in {1..20}; do
    echo $i; a=$((i*10));
    echo "ulimit -t 3000" > todo-$i.sh;
    echo "ulimit -m 4000000" >> todo-$i.sh;
    head -n $a todo | tail -n 10 >> todo-$i.sh; chmod +x todo-$i.sh;
done

for i in {1..20}; do
    ./todo-$i.sh > out-$i &
done
wait
