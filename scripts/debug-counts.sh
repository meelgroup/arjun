#!/bin/bash

f="$1"

rm -f out
rm -f tmp

./arjun --debugminim "tmp" --verb 5 "$f" out | grep "w-debug"
../../ganak/build/ganak --td 0 --arjun 0 --verb 0 "$f"
../../ganak/build/ganak --td 0 --arjun 0 --verb 0 tmp
../../ganak/build/ganak --td 0 --arjun 0 --verb 0 out
