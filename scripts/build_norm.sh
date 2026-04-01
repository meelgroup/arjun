#!/usr/bin/env bash
set -euo pipefail

rm -rf .cmake lib* Test* tests* include tests CM* cmake* arjun Makefile rjun-src
cmake -DENABLE_TESTING=ON -DEXTRA_SYNTH=ON ..
make -j$(nproc)
