#!/bin/bash
set -e

rm -rf lib* Test* tests* include tests CM* cmake* arjun Makefile
cmake -DCMAKE_CXX_COMPILER=clang++ -DCMAKE_C_COMPILER=clang -DENABLE_TESTING=ON ..
make -j26
make test
