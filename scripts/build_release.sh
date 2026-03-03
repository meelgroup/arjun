#!/usr/bin/env bash

set -euo pipefail

rm -rf lib* Test* tests* include tests CM* cmake* arjun Makefile rjun-src
cmake -DENABLE_TESTING=ON -DCMAKE_BUILD_TYPE=Release ..
make -j26
