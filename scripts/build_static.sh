#!/usr/bin/env bash

set -euo pipefail

rm -rf lib* Test* tests* include tests CM* cmake* arjun
cmake -DSTATICCOMPILE=ON -DEXTRA_SYNTH=ON ..
make -j12
strip arjun
