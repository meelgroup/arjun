#!/bin/bash

set -e

rm -rf lib* Test* tests* include tests CM* cmake* arjun
cmake -DCMAKE_BUILD_TYPE=Release -DSTATICCOMPILE=ON ..
make -j12
strip arjun
