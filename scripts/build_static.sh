#!/bin/bash

set -e

rm -rf lib* Test* tests* include tests CM* cmake* arjun
cmake -DSTATICCOMPILE=ON ..
make -j12
strip arjun
