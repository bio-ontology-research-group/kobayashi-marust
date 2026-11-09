#!/bin/bash
# campaign-rest.sh : steps 4, 5 and 3 of campaign.sh (the family step ran first; the ORE inputs before the pools).
T=$(dirname $(readlink -f $0))
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/bridge-nn-term
N48=$S/bin/km-48a; NEW=${NEW:-$S/bin/km-new}
log(){ echo "$(date +%T) $*" >> $S/campaign.log; }
cd $S; export TMPDIR=$S/tmp
# 4. the 16 held-out inputs, 48a then NEW
rm -f $S/runs/summary.tsv
$T/heldout.sh $N48 n48; $T/heldout.sh $NEW new
log heldout done
# 5. the 112 nominal ORE design-half inputs, 48a then NEW
$T/ore_nominal.sh $N48 $NEW
log nominal done
# 3. the gold-backed seed pools, both routes
rm -rf $S/pools/after; $T/pools.sh $NEW after
log pools done
