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
emcmake cmake -DBUILD_SHARED_LIBS=OFF -DCMAKE_BUILD_TYPE=RelWithDebInfo "-DCMAKE_INSTALL_PREFIX=${EMINSTALL}" -DEXTRA_SYNTH=OFF \
    -Dcadical_DIR="${SOLVERS_DIR}/cadical/build" \
    -Dcadiback_DIR="${SOLVERS_DIR}/cadiback/build" \
    -Dcryptominisat5_DIR="${SOLVERS_DIR}/cryptominisat/build" \
    -Dsbva_DIR="${SOLVERS_DIR}/sbva/build" \
    -Dtreedecomp_DIR="${SOLVERS_DIR}/treedecomp/build" \
    ..
emmake make -j$(nproc)
emmake make install
cp arjun.wasm "${SOLVERS_DIR}/arjun/html"
cp "${EMINSTALL}/bin/arjun.js" "${SOLVERS_DIR}/arjun/html"
