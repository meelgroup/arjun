#!/usr/bin/env bash
# Checks the exit code of `arjun --2qbf` on tiny QDIMACS files:
# 10 = true, 20 = false, 1 = rejected. Run from build/.
set -u

tmpd=$(mktemp -d)
trap 'rm -rf "$tmpd"' EXIT
fail=0

check() {
    local expected=$1 name=$2 body=$3
    printf "$body" > "$tmpd/in.qdimacs"
    for cegar in 0 50; do
        ./arjun --2qbf --cegar $cegar "$tmpd/in.qdimacs" > "$tmpd/log" 2>&1
        local ret=$?
        if [ $ret -ne "$expected" ]; then
            echo "FAIL: $name (--cegar $cegar): exit code $ret, expected $expected"
            fail=1
        fi
    done
}

check 10 "y = x1 & x2"         'p cnf 3 3\na 1 2 0\ne 3 0\n1 -3 0\n2 -3 0\n-1 -2 3 0\n'
check 10 "y = x1 xor x2"       'p cnf 3 4\na 1 2 0\ne 3 0\n1 2 -3 0\n-1 -2 -3 0\n1 -2 3 0\n-1 2 3 0\n'
check 20 "no y when x1 = 0"    'p cnf 3 3\na 1 2 0\ne 3 0\n1 3 0\n1 -3 2 0\n-1 3 0\n'
check 20 "contradicting defs"   'p cnf 3 6\na 1 0\ne 2 3 0\n-1 2 0\n1 -2 0\n-1 3 0\n1 -3 0\n2 3 0\n-2 -3 0\n'
check 20 "universal-only clause" 'p cnf 3 2\na 1 2 0\ne 3 0\n1 3 0\n-1 2 0\n'
check 20 "UNSAT matrix"        'p cnf 2 2\na 1 0\ne 2 0\n2 0\n-2 0\n'
check 10 "no universals, SAT"  'p cnf 2 2\ne 1 2 0\n1 2 0\n-1 2 0\n'
check 20 "no prefix, UNSAT"    'p cnf 1 2\n1 0\n-1 0\n'
check 10 "all universal, no clauses" 'p cnf 2 0\na 1 2 0\n'
check 20 "all universal"       'p cnf 2 1\na 1 2 0\n1 -2 0\n'
check 10 "c p show prefix"     'p cnf 2 2\nc p show 1 0\n1 2 0\n-1 -2 0\n'
check 1  "exists-forall-exists" 'p cnf 3 1\ne 1 0\na 2 0\ne 3 0\n1 2 3 0\n'
check 1  "exists-forall"       'p cnf 2 1\ne 1 0\na 2 0\n1 2 0\n'
check 1  "free variable"       'p cnf 3 1\na 1 0\ne 2 0\n1 2 3 0\n'
check 1  "multiplier"          'p cnf 2 1\nc MUST MULTIPLY BY 2\na 1 0\ne 2 0\n1 2 0\n'

# the counterexample must be the universal assignment that has no model
printf 'p cnf 3 3\na 1 2 0\ne 3 0\n-1 3 0\n-1 -3 2 0\n1 3 0\n' > "$tmpd/in.qdimacs"
./arjun --2qbf "$tmpd/in.qdimacs" | grep '^[sV]' | tr '\n' ' ' > "$tmpd/log"
if [ "$(cat "$tmpd/log")" != "s cnf 0 3 3 V 1 0 V -2 0 " ]; then
    echo "FAIL: wrong counterexample: $(cat "$tmpd/log")"
    fail=1
fi

# the functions written for a true formula must work for every universal
# assignment, whether CEGAR or synthesis made them
printf 'p cnf 4 5\na 1 2 0\ne 3 4 0\n1 2 -3 0\n-1 -2 -3 0\n1 -2 3 0\n-1 2 3 0\n3 4 0\n' > "$tmpd/in.qdimacs"
for cegar in 0 50; do
    ./arjun --2qbf --cegar $cegar "$tmpd/in.qdimacs" "$tmpd/skolem.aig" > "$tmpd/log" 2>&1
    if ! ./test-synth -u -q "$tmpd/in.qdimacs" "$tmpd/skolem.aig" | grep -q "verified CORRECT"; then
        echo "FAIL: wrong Skolem functions (--cegar $cegar)"
        fail=1
    fi
done

[ $fail -eq 0 ] && echo "All 2QBF tests passed"
exit $fail
