#!/bin/bash
# pmp.sh <stacksfile> <samples> <delay> <binary> <ontology> <outprefix> [ENV=VAL ...]
# gdb stack samples (every 3 s after <delay> s) of the HT worker child of km classify.
out=$1; n=$2; delay=$3; shift 3
bin=$1
T=$(dirname $0)
$T/run1.sh "$@" &
runner=$!
sleep $delay
: > $out
km=$(pgrep -f "^$bin classify" -n)
for i in $(seq 1 $n); do
  p=$(pgrep -P $km | grep -v "^$" | while read c; do [ "$(cat /proc/$c/comm)" != time ] && echo $c; done | head -1); [ -z "$p" ] && p=$km
  echo "=== $i $p" >> $out
  timeout 30 gdb -p $p -batch -ex "bt 40" 2>/dev/null | grep "^#" >> $out
  sleep 3
done
wait $runner
