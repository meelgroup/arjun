#!/usr/bin/env bash

set -euo pipefail

rm -rf .cmake lib* Test* tests* include tests CM* cmake* arjun Makefile rjun-src deps _deps
cmake -DCMAKE_BUILD_TYPE=Debug -DENABLE_TESTING=ON -DEXTRA_SYNTH=ON \
    -Dcadical_DIR=../../cadical/build \
    -Dcryptominisat5_DIR=../../cryptominisat/build \
    -Dsbva_DIR=../../sbva/build \
    -Dtreedecomp_DIR=../../treedecomp/build \
    -DEvalMaxSAT_DIR=../../EvalMaxSAT/build \
    ..
make -j$(nproc)
make test
