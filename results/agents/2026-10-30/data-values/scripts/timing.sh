#!/bin/bash
# usage: timing.sh <outdir>; each input runs with v1.5.4 and the release candidate side by side (one core each)
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/data-values
out=$1; mkdir -p $out
V154=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/pgo-v154/km-pgo-use
RC=$S/bin/km-v155-rc
for o in ore_ont_10425 ore_ont_15655 ore_ont_5368 ore_ont_10874 ore_ont_4410 ore_ont_4572 ore_ont_7610 qudt-merged; do
  to=600; [ $o = qudt-merged ] && to=1800
  $S/bin/runone.sh $V154 $o $out/v154/$o $to $S/inputs/$o.ttl >> $out/v154.tsv &
  $S/bin/runone.sh $RC $o $out/rc/$o $to $S/inputs/$o.ttl >> $out/rc.tsv &
  wait
done
echo DONE
