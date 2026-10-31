#!/bin/bash
# usage: run1.sh BIN INPUT OUTPREFIX [EXTRA ENV=VAL ...]
bin=$1; in=$2; out=$3; shift 3
export KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1 KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 KM_JSON_GRAPH_EDGES=1 KM_THREADS=1 RAYON_NUM_THREADS=1 OMP_NUM_THREADS=1 KM_ROUTE=auto KM_ROUTING_POLICY=v153 KM_TIMING=1
export TMPDIR=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/subset-unravelling/tmp; mkdir -p $TMPDIR
for kv in "$@"; do export "$kv"; done
s=$(date +%s.%N)
timeout ${TO:-600} taskset -c ${CPU:-0} "$bin" classify "$in" > "$out.out" 2> "$out.err"
rc=$?
e=$(date +%s.%N)
printf "%s\t%s\t%s\t%.2f\n" "$(basename $bin)" "$(basename $in)" "$rc" "$(echo "$e - $s" | bc)"
