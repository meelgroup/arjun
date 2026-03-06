#!/usr/bin/env bash
set -euo pipefail


rm -rf CMake* src cmake* ganak* sharp* Make*
cmake -DANALYZE=ON -DCMAKE_CXX_COMPILER=clang++ -DCMAKE_C_COMPILER=clang -DEXTRA_SYNTH=ON ..
make -j16
