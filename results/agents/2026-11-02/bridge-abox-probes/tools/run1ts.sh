#!/bin/bash
# usage: run1ts.sh <binary> <ontology> <outprefix> [ENV=VAL ...]
# As run1.sh, with stderr lines prefixed by seconds since start (ts -s).
bin=$1; ont=$2; out=$3; shift 3
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/bridge-abox-probes
mkdir -p $S/tmp
start=$(date +%s.%N)
{ env TMPDIR=$S/tmp KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1 \
  KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 KM_THREADS=1 KM_TIMING=1 "$@" \
  /usr/bin/time -v -o $out.time timeout ${KM_RUN_TIMEOUT:-240} $bin classify --lines $ont > $out.out; echo "rc=$?" > $out.rc; } 2>&1 | ts -s "%.s" > $out.err
end=$(date +%s.%N)
rss=$(awk -F: '/Maximum resident/{gsub(/ /,"",$2); print $2}' $out.time)
echo "$(cat $out.rc) wall=$(echo "$end - $start" | bc) maxrss_kb=$rss lines=$(wc -l < $out.out)" | tee $out.summary
