#!/usr/bin/env bash
set -euo pipefail


rm -rf CMake* src cmake* ganak* sharp* Make*
cmake -DANALYZE=ON -DCMAKE_CXX_COMPILER=clang++ -DCMAKE_C_COMPILER=clang -DEXTRA_SYNTH=ON \
    -Dcadical_DIR=../../cadical/build \
    -Dcryptominisat5_DIR=../../cryptominisat/build \
    -Dsbva_DIR=../../sbva/build \
    -Dtreedecomp_DIR=../../treedecomp/build \
    -DEvalMaxSAT_DIR=../../EvalMaxSAT/build \
    ..
make -j$(nproc)
