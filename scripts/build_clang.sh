#!/bin/bash

set -e

rm -rf lib* Test* tests* include tests CM* cmake* arjun Makefile
CXX=clang++ cmake -DENABLE_TESTING=ON ..
make -j26
make test
