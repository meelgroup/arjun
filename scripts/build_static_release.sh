#!/usr/bin/env bash

set -euo pipefail

SOLVERS_DIR="$(cd "$(dirname "$0")/../.." && pwd)"

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
cmake -DCMAKE_BUILD_TYPE=Release -DBUILD_SHARED_LIBS=OFF \
    -Dcadiback_DIR="${SOLVERS_DIR}/cadiback/build" \
    -Dcadical_DIR="${SOLVERS_DIR}/cadical/build" \
    -Dcryptominisat5_DIR="${SOLVERS_DIR}/cryptominisat/build" \
    -Dsbva_DIR="${SOLVERS_DIR}/sbva/build" \
    -Dtreedecomp_DIR="${SOLVERS_DIR}/treedecomp/build" \
    -DGMPXX_LIBRARY=/usr/local/lib/libgmpxx.a \
    ..
make -j$(nproc)
strip arjun
