#!/bin/bash
# usage: run.sh BIN INPUT OUTPREFIX [timeout] [cpu]
# Release flags, KM_THREADS=1, one CPU. timeout(1) kills the whole tree via its own group.
BIN=$1; IN=$2; OUT=$3; TO=${4:-240}; CPU=${5:-3}
export KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1 KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 KM_THREADS=1
export TMPDIR=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/perf-9027/tmp
mkdir -p $TMPDIR
s=$(date +%s.%N)
timeout -s KILL $TO taskset -c $CPU $BIN classify --lines $IN > $OUT.out 2> $OUT.err
rc=$?
e=$(date +%s.%N)
w=$(echo "$e - $s" | bc)
subs=$(grep -c '^SUB' $OUT.out)
echo "$(basename $IN .owl) $(basename $BIN) rc=$rc wall=$w subs=$subs $(head -2 $OUT.out | tr '\n' ' ')"
