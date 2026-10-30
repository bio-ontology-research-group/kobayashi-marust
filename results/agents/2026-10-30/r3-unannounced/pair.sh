#!/bin/bash
# pair.sh FILE: km.final nominals, fix then v1.5.4 rules on the same binary, 60 s cap each
f=$1; d=$(dirname $0)/..
for e in "X=1" "KM_CONTEXT_UNIT_R3=1 KM_CONTEXT_NO_EQ_R2=1"; do
  s=$(date +%s.%N); env $e KM_ROUTE=nominals timeout 60 $d/km.final classify --lines $f > /dev/null 2>&1; rc=$?
  printf "%s\t%s\t%s\t%.2f\n" "$f" "$e" "$rc" "$(echo "$(date +%s.%N)-$s"|bc)"
done
