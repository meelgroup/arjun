#!/usr/bin/env bash
# Build CMS at the currently checked-out commit of ../cryptominisat-bisect plus an
# arjun against it, then report how many vars puura failed to define on the
# bobtuint10neg benchmark. 0 = good (old behaviour), >0 = regressed.
set -uo pipefail
S=/home/soos/development/sat_solvers
CMS=$S/cryptominisat-bisect
ARJ=$S/arjun-bisect/build_bisect
BENCH=$S/arjun/build/benchmarks-qdimacs/bobtuint10neg_all_bit_differing_from_cycle.qdimacs.gz

mkdir -p "$CMS/build" "$ARJ"
cd "$CMS/build" || exit 125
cmake -DENABLE_TESTING=OFF -DCMAKE_BUILD_TYPE=RelWithDebInfo -DBUILD_SHARED_LIBS=ON \
  -DENABLE_ASSERTIONS=ON -Dcadical_DIR=$S/cadical/build -Dcadiback_DIR=$S/cadiback/build \
  .. > cmake.log 2>&1 || { echo "SKIP cmake"; exit 125; }
make -j$(nproc) > make.log 2>&1 || { echo "SKIP cms-build"; exit 125; }

cd "$ARJ" || exit 125
cmake -DENABLE_TESTING=OFF -DEXTRA_SYNTH=ON -DCMAKE_BUILD_TYPE=RelWithDebInfo \
  -Dcadical_DIR=$S/cadical/build -Dcadiback_DIR=$S/cadiback/build \
  -Dcryptominisat5_DIR=$CMS/build -Dsbva_DIR=$S/sbva/build \
  -DEvalMaxSAT_DIR=$S/EvalMaxSAT/build ../ > cmake.log 2>&1 || { echo "SKIP arj-cmake"; exit 125; }
make -j$(nproc) arjun-bin > make.log 2>&1 || { echo "SKIP arj-build"; exit 125; }

OUT=$(timeout 120 ./arjun --verb 1 --synth "$BENCH" 2>&1 | grep -oP 'still to-define: \K[0-9]+' | tail -1)
[ -z "$OUT" ] && { echo "TIMEOUT/none -> BAD"; exit 1; }
echo "still-to-define: $OUT"
[ "$OUT" -eq 0 ] && exit 0 || exit 1
