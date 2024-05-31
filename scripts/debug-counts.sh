#!/bin/bash

f="$1"

rm -f out
rm -f tmp
rm -f tmp-renum

./arjun --debugminim "tmp" --verb 5 "$f" out > verb
grep "w-debug" verb
../../ganak/build/ganak --td 0 --arjun 0 --verb 0 "$f"
../../ganak/build/ganak --td 0 --arjun 0 --verb 0 tmp
../../ganak/build/ganak --td 0 --arjun 0 --verb 0 out
