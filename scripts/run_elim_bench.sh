#!/bin/bash
# Quick sanity bench: run arjun on a CNF and print the headline counts
# (vars, indep, bin cls, long cls, lits, T). Intended for quick A/B testing
# of simplification tweaks.
#
# Usage:
#   ./run_elim_bench.sh <cnf[.gz]> [arjun-args...]
# Assumes the `arjun` binary and `count_literals.py` live in the caller's cwd
# (typically arjun/build).

set -e
CNF="${1:?usage: $0 <cnf[.gz]> [arjun-args...]}"
shift || true

rm -f /tmp/arjun_elim_out
LOG=/tmp/arjun_elim.log
./arjun --verb 1 "$@" "$CNF" /tmp/arjun_elim_out > "$LOG" 2>&1

T=$(awk '/\[arjun\] All done/ {print $NF}' "$LOG")
OUT=$(./count_literals.py /tmp/arjun_elim_out)
VARS=$(echo "$OUT" | awk '/^num \(non-set\) vars/ {print $NF}')
BIN=$(echo "$OUT" | awk '/^num bin cls/ {print $NF}')
LONG=$(echo "$OUT" | awk '/^num long cls/ {print $NF}')
LITS=$(echo "$OUT" | awk '/^num \(non-unit\) lits/ {print $NF}')
INDEP=$(echo "$OUT" | awk '/^indep size/ {print $NF}')
OPTINDEP=$(echo "$OUT" | awk '/^opt indep size/ {print $NF}')

printf "%-32s vars=%-5s indep=%-5s optind=%-5s bin=%-5s long=%-5s lits=%-7s T=%s\n" \
    "$(basename "$CNF")" "$VARS" "$INDEP" "$OPTINDEP" "$BIN" "$LONG" "$LITS" "$T"
