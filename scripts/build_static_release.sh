#!/usr/bin/env bash

set -euo pipefail

rm -rf lib* Test* tests* include tests CM* cmake* arjun
cmake -DCMAKE_BUILD_TYPE=Release -DSTATICCOMPILE=ON \
    -Dcadical_DIR=../../cadical/build \
    -Dcryptominisat5_DIR=../../cryptominisat/build \
    -Dsbva_DIR=../../sbva/build \
    -Dtreedecomp_DIR=../../treedecomp/build \
    ..
make -j$(nproc)
strip arjun
