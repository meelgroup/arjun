#!/usr/bin/env bash

set -euo pipefail

rm -rf .cmake
rm -rf lib*
rm -rf Test*
rm -rf tests*
rm -rf include
rm -rf tests
rm -rf arjun
rm -rf Makefile
rm -rf src
rm -rf CM*
rm -rf cmake*
rm -rf deps
rm -rf _deps
SOLVERS_DIR="$(cd "$(dirname "$0")/../.." && pwd)"
echo "solvers dir: $SOLVERS_DIR"
cmake -DENABLE_TESTING=ON \
    -DEXTRA_SYNTH=ON \
    -Dcadical_DIR="${SOLVERS_DIR}/cadical/build" \
    -Dcadiback_DIR="${SOLVERS_DIR}/cadiback/build" \
    -Dcryptominisat5_DIR="${SOLVERS_DIR}/cryptominisat/build" \
    -Dsbva_DIR="${SOLVERS_DIR}/sbva/build" \
    -Dtreedecomp_DIR="${SOLVERS_DIR}/treedecomp/build" \
    -DEvalMaxSAT_DIR="${SOLVERS_DIR}/EvalMaxSAT/build" \
    ..
make -j$(nproc)
make test
