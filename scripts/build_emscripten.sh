#!/usr/bin/env bash
set -euo pipefail

rm -rf lib* Test* tests* include tests CM* cmake* arjun Makefile rjun-src
emcmake cmake -DSTATICCOMPILE=ON -DCMAKE_BUILD_TYPE=RelWithDebInfo -DSTATICCOMPILE=ON "-DCMAKE_INSTALL_PREFIX=${EMINSTALL}" -DEXTRA_SYNTH=OFF \
    -Dcadical_DIR=../../cadical/build \
    -Dcryptominisat5_DIR=../../cryptominisat/build \
    -Dsbva_DIR=../../sbva/build \
    -Dtreedecomp_DIR=../../treedecomp/build \
    ..
emmake make -j$(nproc)
emmake make install
cp arjun.wasm ../html
cp "${EMINSTALL}/bin/arjun.js" ../html
