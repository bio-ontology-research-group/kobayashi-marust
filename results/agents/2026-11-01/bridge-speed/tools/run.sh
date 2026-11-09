#!/bin/bash
# usage: run.sh BIN ONT OUTPREFIX [extra args...]
BIN=$1; ONT=$2; OUT=$3; shift 3
export KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1 KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 KM_THREADS=1 KM_TIMING=1
F=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/v150-corpus/files/ore_ont_$ONT.owl
s=$(date +%s.%N)
timeout ${TO:-240} "$BIN" classify --lines "$@" "$F" > $OUT.out 2> $OUT.err
rc=$?
e=$(date +%s.%N)
echo "$ONT rc=$rc wall=$(echo "$e - $s" | bc) lines=$(wc -l < $OUT.out)" | tee -a $OUT.time
