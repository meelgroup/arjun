#!/usr/bin/env bash
set -euo pipefail

rm -rf lib* Test* tests* include tests CM* cmake* arjun Makefile
cmake -DCMAKE_CXX_COMPILER=clang++ -DCMAKE_C_COMPILER=clang -DENABLE_TESTING=ON -DEXTRA_SYNTH=ON ..
make -j26
make test
