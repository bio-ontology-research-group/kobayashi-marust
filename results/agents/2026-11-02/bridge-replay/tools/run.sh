#!/bin/bash
# usage: run.sh BIN ONT OUTPREFIX [extra classify args...]
# One release-flag run on the automatic route (unless KM_ROUTE is set by the
# caller), --lines, timeout ${TO:-240}, peak RSS from /usr/bin/time -v.
BIN=$1; ONT=$2; OUT=$3; shift 3
export KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1 KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 KM_THREADS=1 KM_TIMING=1
export TMPDIR=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/bridge-replay/tmp
mkdir -p $TMPDIR
F=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/v150-corpus/files/ore_ont_$ONT.owl
s=$(date +%s.%N)
/usr/bin/time -v -o $OUT.rss timeout ${TO:-240} "$BIN" classify --lines "$@" "$F" > $OUT.out 2> $OUT.err
rc=$?
e=$(date +%s.%N)
rss=$(awk -F: '/Maximum resident/ {gsub(/ /,"",$2); print $2}' $OUT.rss)
echo "$ONT rc=$rc wall=$(echo "$e - $s" | bc) rss_kb=$rss lines=$(wc -l < $OUT.out)" | tee -a $OUT.time
