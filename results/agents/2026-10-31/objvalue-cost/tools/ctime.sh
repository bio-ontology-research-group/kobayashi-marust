#!/bin/bash
# ctime.sh CPU BIN CAP ROUTE FILE... : km classify --lines wall time on one pinned CPU, verdict vs cached HermiT gold (r3-unannounced/gold/<stem>.json)
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/objvalue-cost
G=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/r3-unannounced/gold
CPU=$1; B=$2; C=$3; RT=$4; shift 4
for f in "$@"; do stem=$(basename $f .ofn); s=$(date +%s.%N)
  if [ $RT = auto ]; then out=$(env -u KM_ROUTE KM_THREADS=1 timeout $C taskset -c $CPU $B classify --lines $f 2>/dev/null); else out=$(env KM_ROUTE=$RT KM_THREADS=1 timeout $C taskset -c $CPU $B classify --lines $f 2>/dev/null); fi
  rc=$?; t=$(echo "$(date +%s.%N)-$s"|bc)
  g=$G/$stem.json; [ -f ${f%.ofn}.hermit.json ] && g=${f%.ofn}.hermit.json
  if [ -f $g ]; then v=$(python3 -I $S/verdict.py $g <<< "$out"); else v=nogold; fi
  printf "%s\t%s\t%s\t%s\t%.2f\t%s\n" $stem $(basename $B) $RT $rc $t "$v"; done
