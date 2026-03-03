#!/usr/bin/env bash

set -euo pipefail

rm -rf .cmake lib* Test* tests* include tests CM* cmake* arjun
cmake -DCMAKE_BUILD_TYPE=Debug -DENABLE_TESTING=ON ..
make -j6
make test
