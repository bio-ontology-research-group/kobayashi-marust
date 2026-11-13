#!/bin/bash
# Interleaved timing: v1.5.3 vs v1.6.2-rc PGO, one km at a time, KM_THREADS=1.
A=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/v153-release-assets-b5abf83a/km-v1.5.3-linux-x86_64
B=/mnt/data1/leechuck/km-work/v162/measure/pgo/km-v1.6.2-rc-pgo
C=/mnt/data1/leechuck/km-work/v161/assets-37e75e28/km-v1.6.1-linux-x86_64
export OMP_NUM_THREADS=1 RAYON_NUM_THREADS=1 KM_THREADS=1 KM_ROUTE=auto KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1 KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 KM_JSON_GRAPH_EDGES=1
out=$PWD/out; mkdir -p $out
for rep in 1 2 3 4 5; do
  while read p; do
    for v in A B C; do
      bin=${!v}; s=$(date +%s.%N)
      timeout 300 $bin classify "$p" >$out/tax.$v 2>/dev/null; rc=$?
      e=$(date +%s.%N); echo "$rep $v $(basename $p .owl) $rc $(echo "$e - $s" | bc)"
    done
  done < inputs.txt
done > times.txt
echo BENCH-DONE
