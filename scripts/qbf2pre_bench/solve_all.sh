#!/bin/bash
# usage, from build/: ../scripts/qbf2pre_bench/solve_all.sh PRE
# Runs cadet, caqe, rareqs and depqbf on the outputs of preprocessor PRE (see bench.py).
D=$(dirname "$(readlink -f "$0")"); Q=$D/../../qbf_solvers
export TOUT=${TOUT:-20} JOBS=${JOBS:-1}
python3 $D/bench.py solve $1 cadet "$Q/cadet/cadet %i"
python3 $D/bench.py solve $1 caqe "$Q/caqe/target/release/caqe %i"
python3 $D/bench.py solve $1 rareqs "$Q/rareqs/rareqs-1.1/rareqs %i"
python3 $D/bench.py solve $1 depqbf "$Q/depqbf/depqbf %i"
