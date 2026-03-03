#!/bin/bash
set -e

rm -rf lib* Test* tests* include tests CM* cmake* arjun Makefile rjun-src
emcmake cmake -DCMAKE_BUILD_TYPE=Debug -DCMAKE_INSTALL_PREFIX=$EMINSTALL -DEXTRA_SYNTH=OFF ..
emmake make -j26
emmake make install
cp arjun.wasm ../html
cp $EMINSTALL/bin/arjun.js ../html
