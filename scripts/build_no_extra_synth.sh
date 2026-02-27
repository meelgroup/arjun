#!/bin/bash

set -e

rm -rf lib* Test* tests* include tests CM* cmake* arjun Makefile rjun-src
cmake -DEXTRA_SYNTH=OFF -DENABLE_TESTING=OFF ..
make -j26
