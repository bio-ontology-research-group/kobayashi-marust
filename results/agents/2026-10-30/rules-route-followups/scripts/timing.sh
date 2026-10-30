#!/bin/bash
# timing.sh OUT REPS: interleaved runs of 7278 and 3726, previous agent's run1 env, wall and CPU seconds
out=$1; reps=$2; mkdir -p $out/runs
export KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1 KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 KM_JSON_GRAPH_EDGES=1 KM_THREADS=1 RAYON_NUM_THREADS=1 OMP_NUM_THREADS=1 KM_ROUTE=auto KM_ROUTING_POLICY=v153 KM_TIMING=1 TMPDIR=$HOME/tmp
S=$(dirname $(readlink -f $0))
for r in $(seq 1 $reps); do for o in 7278 3726; do for cfg in base i12 final final-nomemo; do
  b=$S/km-${cfg%-nomemo}; [ $cfg = base ] && b=$S/km-base; extra=""; [ $cfg = final-nomemo ] && extra="KM_NO_FRONTEND_PASS_CACHE=1"
  p=$out/runs/$cfg-$o-$r
  /usr/bin/time -f "%e %U %S" -o $p.time env $extra timeout 300 taskset -c ${CPU:-44} $b classify $S/inputs/ore_ont_$o.owl > $p.out 2> $p.err
  echo -e "$cfg\t$o\t$r\t$?\t$(cat $p.time | tr ' ' '\t')\t$(md5sum < $p.out | cut -c1-12)" >> $out/table.tsv
done; done; done
