#!/bin/bash
# set60.sh BIN TAG LIST [ENV...]: nominals route, 60 s cap, one at a time, files relative to the r3 scratch
B=$(readlink -f $1); TAG=$2; L=$(readlink -f $3); shift 3
OUT=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/nominal-r1600/set60-$TAG.tsv
cd /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/r3-unannounced
while read f; do s=$(date +%s.%N); env "$@" KM_ROUTE=nominals timeout 60 $B classify --lines $f > /dev/null 2>&1; rc=$?; printf "%s\t%s\t%s\t%.2f\n" $f $TAG $rc $(echo "$(date +%s.%N)-$s"|bc) >> $OUT; done < $L
echo DONE >> $OUT
