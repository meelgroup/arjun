#!/bin/bash

set -e

rm -rf lib* Test* tests* include tests CM* cmake* arjun Makefile
cmake -DENABLE_TESTING=ON ..
make -j6
make test
