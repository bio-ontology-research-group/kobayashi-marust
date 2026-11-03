#!/bin/bash
# campaign.sh : every measurement of this branch, one step after another,
# never more than two KM processes at a time. BASE = acf6df9a, NEW = the fix.
T=$(dirname $(readlink -f $0))
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/bridge-reflexive
BASE=$S/bin/km-base; NEW=${NEW:-$S/bin/km-v3}
log(){ echo "$(date +%T) $*" >> $S/campaign.log; }
cd $S
log start NEW=$NEW
# 1. the five seeds, the two reductions and the three new reductions, 20 runs, both routes
rm -f $S/seeds20/final.tsv
FAM_FORCED_TIMEOUT=60 python3 -I $T/fam_run.py $NEW $S/seeds20/gold $S/seeds20/final.tsv ht_bridge,auto 20 $S/seeds20/*.ofn
log seeds20 done
# 2. the sibling family: runs 2 and 3 on NEW (run 1 is famrun/v3-1.tsv), run 1 on BASE
FAM_TIMEOUT=60 FAM_FORCED_TIMEOUT=30 python3 -I $T/fam_run.py $NEW $S/fam/gold $S/famrun/v3-23.tsv ht_bridge,auto 2 $S/fam/seeds/*.ofn
log family new done
FAM_TIMEOUT=60 FAM_FORCED_TIMEOUT=30 python3 -I $T/fam_run.py $BASE $S/fam/gold $S/famrun/base-1.tsv ht_bridge,auto 1 $S/fam/seeds/*.ofn
log family base done
# 3. the seed pools, NEW on every seed
$T/pools.sh $NEW after
log pools after done
# 4. held-out 16, base and new
$T/heldout.sh $BASE base; $T/heldout.sh $NEW new
log heldout done
# 5. 112 nominal ORE inputs
$T/ore_nominal.sh $BASE $NEW
log nominal done
