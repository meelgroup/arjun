#!/bin/sh
# lit's internal shell has no $?: expect_exit N cmd... fails unless cmd exits with N
want=$1; shift
"$@"; got=$?
[ "$got" -eq "$want" ] || { echo "exit code $got, expected $want" >&2; exit 1; }
