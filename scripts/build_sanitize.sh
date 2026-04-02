#!/usr/bin/env bash
set -euo pipefail

rm -rf lib* Test* tests* include tests CM* cmake* arjun Makefile
cmake -DCMAKE_CXX_COMPILER=clang++ -DCMAKE_C_COMPILER=clang -DENABLE_TESTING=ON -DSANITIZE=ON -DEXTRA_SYNTH=ON \
    -Dcadical_DIR=../../cadical/build \
    -Dcryptominisat5_DIR=../../cryptominisat/build \
    -Dsbva_DIR=../../sbva/build \
    -Dtreedecomp_DIR=../../treedecomp/build \
    -DEvalMaxSAT_DIR=../../EvalMaxSAT/build \
    ..
make -j$(nproc)
make test
