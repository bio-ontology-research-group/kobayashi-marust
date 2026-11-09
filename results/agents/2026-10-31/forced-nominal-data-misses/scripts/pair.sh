#!/bin/bash
# usage: pair.sh <rounds> <ontology names...>; alternates base and fix2 on one CPU each, scope environment, prints wall seconds
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/forced-nominal-data-misses
IN=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/data-values/scope/inputs
n=$1; shift
export TMPDIR=$S/tmp/pair OMP_NUM_THREADS=1 RAYON_NUM_THREADS=1 KM_THREADS=1 KM_ROUTE=auto
export KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1 KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 KM_JSON_GRAPH_EDGES=1
mkdir -p $TMPDIR
for o in "$@"; do
  for i in $(seq $n); do
    for b in base fix2; do
      s=$(date +%s.%N); timeout 240 $S/tools/one-$b classify $IN/$o.owl > /dev/null 2>&1; e=$(date +%s.%N)
      printf "%s\t%s\t%s\t%.2f\n" "$o" "$b" "$i" "$(echo "$e - $s" | bc)"
    done
  done
done
