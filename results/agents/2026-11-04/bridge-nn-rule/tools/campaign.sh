#!/bin/bash
# campaign.sh : every KM measurement of this branch, one step after another,
# never more than two KM processes at a time. BASE = 1ffee4a6, NEW = the fix.
T=$(dirname $(readlink -f $0))
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/bridge-nn-rule
BASE=$S/bin/km-base; NEW=${NEW:-$S/bin/km-new}
log(){ echo "$(date +%T) $*" >> $S/campaign.log; }
cd $S
log start NEW=$NEW
# 1. the two reductions and the two seeds, 20 runs, both routes
rm -f $S/red20-new.tsv
FAM_FORCED_TIMEOUT=60 python3 -I $T/fam_run.py $NEW $S/gold $S/red20-new.tsv ht_bridge,auto 20 $S/red/*.ofn
log red20 done
# 2. the seed pools, NEW on every seed
$T/pools.sh $NEW after
log pools after done
# 3. held-out 16, base and new
$T/heldout.sh $BASE base; $T/heldout.sh $NEW new
log heldout done
# 4. 112 nominal ORE inputs
$T/ore_nominal.sh $BASE $NEW
log nominal done
# 5. the sibling family (after its HermiT gold is complete)
# three runs on NEW, one on BASE
while ! grep -q "^gold:" $S/gold.log; do sleep 30; done
mkdir -p $S/famrun; rm -f $S/famrun/new.tsv $S/famrun/base.tsv
FAM_TIMEOUT=60 FAM_FORCED_TIMEOUT=30 python3 -I $T/fam_run.py $NEW $S/fam/gold $S/famrun/new.tsv ht_bridge,auto 3 $S/fam/seeds/*.ofn
log family new done
FAM_TIMEOUT=60 FAM_FORCED_TIMEOUT=30 python3 -I $T/fam_run.py $BASE $S/fam/gold $S/famrun/base.tsv ht_bridge,auto 1 $S/fam/seeds/*.ofn
log family base done
