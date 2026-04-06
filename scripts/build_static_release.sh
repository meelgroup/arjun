#!/usr/bin/env bash

set -euo pipefail

SOLVERS_DIR="$(cd "$(dirname "$0")/../.." && pwd)"

rm -rf .cmake
rm -rf lib*
rm -rf Test*
rm -rf tests*
rm -rf include
rm -rf tests
rm -rf CM*
rm -rf cmake*
rm -rf arjun
rm -rf Makefile
rm -rf rjun-src
rm -rf deps
rm -rf _deps
cmake -DCMAKE_BUILD_TYPE=Release -DBUILD_SHARED_LIBS=OFF \
    -Dcadiback_DIR="${SOLVERS_DIR}/cadiback/build" \
    -Dcadical_DIR="${SOLVERS_DIR}/cadical/build" \
    -Dcryptominisat5_DIR="${SOLVERS_DIR}/cryptominisat/build" \
    -Dsbva_DIR="${SOLVERS_DIR}/sbva/build" \
    -Dtreedecomp_DIR="${SOLVERS_DIR}/treedecomp/build" \
    -DGMPXX_LIBRARY=/usr/local/lib/libgmpxx.a \
    ..
make -j$(nproc)
strip arjun

# Get SHA1 hashes and build versioned filename
HASHES=$(./arjun -v 2>&1 || true)
ARJUN_SHA=$(echo "$HASHES" | grep "Arjun SHA1" | grep -oP '[0-9a-f]{40}' | cut -c1-8)
SBVA_SHA=$(echo "$HASHES" | grep "SBVA SHA1" | grep -oP '[0-9a-f]{40}' | cut -c1-8)
CMS_SHA=$(echo "$HASHES" | grep "CMS SHA1" | grep -oP '[0-9a-f]{40}' | cut -c1-8)

DEST="arjun_${ARJUN_SHA}_${SBVA_SHA}_${CMS_SHA}"
cp arjun "$DEST"
echo "Copied to $DEST"
