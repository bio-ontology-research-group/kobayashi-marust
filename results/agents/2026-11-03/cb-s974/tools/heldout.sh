#!/bin/bash
# heldout.sh BIN LABEL [K=V ...] : the 16 held-out inputs of docs/V1.5.5-STATUS.md
# ("Konclude coverage gap"), release flags, 240 s, two at a time, 12128 alone.
# Rows go to .work/agent-scratch/cb-s974/runs/summary.tsv (tools/one.sh).
T=$(dirname $(readlink -f $0)); BIN=$1; L=$2; shift 2
set -- "$@"
EXTRA=("$@")
pairs="4903:11647 4796:3917 11378:12191 9151:9577 6132:9899 16315:10838 3087:7557 10926"
for p in $pairs; do
  a=${p%%:*}; b=${p#*:}
  if [ "$a" = "$b" ]; then $T/one.sh $BIN $a $L "${EXTRA[@]}"; continue; fi
  $T/one.sh $BIN $a $L "${EXTRA[@]}" & $T/one.sh $BIN $b $L "${EXTRA[@]}" & wait
done
$T/one.sh $BIN 12128 $L "${EXTRA[@]}"
