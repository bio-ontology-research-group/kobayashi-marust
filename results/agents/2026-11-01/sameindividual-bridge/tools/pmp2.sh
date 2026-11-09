#!/bin/bash
# pmp2.sh <stacksfile> <samples> <delay> -- run1.sh args : gdb stack samples of the worker child ("exe") of the km supervisor.
out=$1; n=$2; delay=$3; shift 4
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/sameindividual-bridge
$S/tools/run1.sh "$@" &
runner=$!
sleep $delay
: > $out
km=$(pgrep -f "$S/km.v[0-9a-z]* classify" -n)
for i in $(seq 1 $n); do
  p=$(pgrep -P $km | head -1); [ -z "$p" ] && p=$km
  echo "=== $i $p" >> $out
  timeout 30 gdb -p $p -batch -ex "bt 30" 2>/dev/null | grep "^#" >> $out
  sleep 4
done
wait $runner
