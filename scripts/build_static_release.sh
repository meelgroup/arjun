#!/usr/bin/env bash

set -euo pipefail

rm -rf lib* Test* tests* include tests CM* cmake* arjun
cmake -DCMAKE_BUILD_TYPE=Release -DSTATICCOMPILE=ON ..
make -j$(nproc)
strip arjun
