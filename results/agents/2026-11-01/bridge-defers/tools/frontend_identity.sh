#!/bin/bash
# usage: frontend_identity.sh BASE_KM NEW_KM FILE... ; prints "same|DIFF|ERR file"
# Compares the `km ofn` clause output of two binaries byte for byte.
B=$1; N=$2; shift 2
for f in "$@"; do
  a=$(timeout 120 $B ofn "$f" 2>/dev/null | md5sum | cut -d' ' -f1); ra=${PIPESTATUS[0]}
  b=$(timeout 120 $N ofn "$f" 2>/dev/null | md5sum | cut -d' ' -f1)
  if [ "$a" = "$b" ]; then echo "same $f"; else echo "DIFF $f"; fi
done
