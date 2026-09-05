#!/usr/bin/env bash
# Run arjun --synth over the qdimacs benchmark set and print, per benchmark, how
# many variables puura failed to define and the total time.
# usage: sweep_puura.sh <arjun-binary> <out.csv> <timeout-s> <jobs> [extra arjun args...]
set -uo pipefail
BIN=$(readlink -f "$1"); OUT=$2; TO=$3; JOBS=$4; shift 4
BENCH_DIR=$(cd "$(dirname "$0")/../build/benchmarks-qdimacs" && pwd)
export BIN TO EXTRA="$*"
run_one() {
    b=$(basename "$1")
    log=$(timeout "$TO" "$BIN" --verb 1 --synth $EXTRA "$1" 2>&1 | tr -d '\033')
    td=$(echo "$log" | grep -oE '\[puura\] Done.*still to-define: [0-9]+' | grep -oE '[0-9]+$' | head -1)
    t=$(echo "$log"  | grep -oE 'All done\. T: [0-9.]+' | grep -oE '[0-9.]+$' | head -1)
    echo "$b,${td:-NA},${t:-TO}"
}
export -f run_one
{ echo "bench,to_define,time"; ls "$BENCH_DIR"/*.qdimacs.gz | xargs -P "$JOBS" -I{} bash -c 'run_one "$@"' _ {}; } > "$OUT"
