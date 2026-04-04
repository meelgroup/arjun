#!/usr/bin/env bash
set -euo pipefail

rm -rf .cmake
rm -rf lib*
rm -rf Test*
rm -rf tests*
rm -rf include
rm -rf tests
rm -rf CM*
rm -rf cmake*
rm -rf arjun
rm -rf Makefile
rm -rf rjun-src
rm -rf deps
rm -rf _deps
cmake -DCMAKE_CXX_COMPILER=clang++ -DCMAKE_C_COMPILER=clang -DENABLE_TESTING=ON -DEXTRA_SYNTH=ON \
    -Dcadical_DIR=../../cadical/build \
    -Dcadiback_DIR=../../cadiback/build \
    -Dcryptominisat5_DIR=../../cryptominisat/build \
    -Dsbva_DIR=../../sbva/build \
    -Dtreedecomp_DIR=../../treedecomp/build \
    -DEvalMaxSAT_DIR=../../EvalMaxSAT/build \
    ..
make -j$(nproc)
make test
