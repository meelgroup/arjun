#!/bin/bash
# What still fires on a preprocessor's output? bloqqer with one technique on at a time, and
# qratpre+, each printing the size of what it leaves. usage: ablate.sh FILE.qdimacs...
Q=$(dirname "$(readlink -f "$0")")/../../qbf_solvers
B=$Q/bloqqer/bloqqer-037-8660cb9-151127/bloqqer; QP=$Q/qratpreplus/qratpre+
ALL="bce ble hte cce hbce eq ve exp"
st() { python3 - "$1" <<'PY'
import sys
u=set(); c=l=ul=0; ex=set(); empty=False; seen=False
try:
    for line in open(sys.argv[1]):
        t=line.split()
        if not t or t[0]=='c': continue
        if t[0]=='p': seen=True; continue
        if t[0]=='a': u.update(int(x) for x in t[1:-1]); continue
        if t[0]=='e': continue
        lits=[int(x) for x in t[:-1]]
        if not lits: empty=True
        c+=1; l+=len(lits); ul+=sum(abs(x) in u for x in lits); ex.update(abs(x) for x in lits if abs(x) not in u)
except Exception: pass
print("%s cls=%d lits=%d ulits=%d ex=%d" % ("FALSE" if empty else "TRUE" if seen and c==0 else "-" if seen else "FAIL", c,l,ul,len(ex)))
PY
}
for f in "$@"; do
  b=$(basename $f); T=$(mktemp)
  echo "$b in: $(st $f)"
  off=""; for x in $ALL; do off="$off --no-$x"; done
  timeout 60 $B $off $f > $T 2>/dev/null; echo "$b bloqqer-none: $(st $T)"
  for on in ble hte cce "bce hbce" bce eq ve exp; do
    off=""; for x in $ALL; do [[ " $on " == *" $x "* ]] || off="$off --no-$x"; done
    timeout 60 $B $off $f > $T 2>/dev/null; echo "$b bloqqer-only-${on// /+}: $(st $T)"
  done
  timeout 60 $B $f > $T 2>/dev/null; echo "$b bloqqer-full: $(st $T)"
  timeout 60 $QP --print-formula --no-qat --no-qrate --no-qratu --no-ble $f 2>/dev/null > $T; echo "$b qrat-qbce-only: $(st $T)"
  timeout 60 $QP --print-formula --no-qrate --no-qratu --no-ble $f 2>/dev/null > $T; echo "$b qrat-qbce+qat: $(st $T)"
  timeout 60 $QP --print-formula --no-qratu --no-ble $f 2>/dev/null > $T; echo "$b qrat-qbce+qat+qrate: $(st $T)"
  timeout 60 $QP --print-formula --no-qat --no-qrate --no-qratu $f 2>/dev/null > $T; echo "$b qrat-qbce+ble: $(st $T)"
  timeout 60 $QP --print-formula $f 2>/dev/null > $T; echo "$b qrat-full: $(st $T)"
  rm -f $T
done
