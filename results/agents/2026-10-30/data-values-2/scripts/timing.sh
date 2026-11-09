#!/bin/bash
# usage: timing.sh <outdir> <binA> <binB>; each input runs with both binaries side by side (one core each)
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/data-values-2
out=$1; A=$2; B=$3; mkdir -p $out
for o in ore_ont_10425 ore_ont_15655 ore_ont_5368 ore_ont_10874 ore_ont_4410 ore_ont_4572 ore_ont_7610; do
  $S/bin/runone.sh $A $o $out/a/$o 600 >> $out/a.tsv &
  $S/bin/runone.sh $B $o $out/b/$o 600 >> $out/b.tsv &
  wait
done
echo DONE
