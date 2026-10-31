#!/bin/bash
# usage: lost.sh BIN SEED...   one core each, ht_general, certificates checked inline
bin=$1; shift
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/subset-unravelling
for seed in "$@"; do
  d=$(mktemp -d -p $S/tmp); 
  s=$(date +%s.%N)
  env -i PATH=$PATH HOME=$HOME KM_ROUTE=ht_general KM_THREADS=1 RAYON_NUM_THREADS=1 TMPDIR=$d KM_HT_SUBSET_MODEL_CERT=$d KM_HT_SUBSET_MODEL_CHECKER=$S/bin/ht-subset-unravelling-check \
    timeout ${TO:-60} "$bin" classify --lines $S/runs/alci/ont/g$seed.ofn > $d/out 2> $d/err
  rc=$?; e=$(date +%s.%N)
  printf "%s\t%s\trc=%s\t%.1fs\tacc=%s\trej=%s\tnoemit=%s\tpred=%s\tmd5=%s\n" $seed $(basename $bin) $rc $(echo "$e - $s"|bc) \
    $(grep -c ' accepted$' $d/err) $(grep -c ' rejected$' $d/err) $(grep -c 'not emitted' $d/err) $(grep -c 'variant=relabel+predecessor accepted' $d/err) $(sort $d/out | md5sum | cut -c1-8)
  rm -rf $d
done
