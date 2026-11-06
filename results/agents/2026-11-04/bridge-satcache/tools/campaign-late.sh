#!/bin/bash
# campaign.sh : every KM measurement of this branch, one step after another,
# never more than two KM processes at a time (adapted from
# results/agents/2026-11-04/bridge-nn-rule/tools/campaign.sh).
# BASE = 48a1113b, NEW = the fix (LTO release builds of both).
T=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/fix-bridge-satcache/results/agents/2026-11-04/bridge-satcache/tools
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/bridge-satcache
BASE=$S/bin/km-base; NEW=${NEW:-$S/bin/km-new}
log(){ echo "$(date +%T) $*" >> $S/campaign.log; }
cd $S
log start NEW=$NEW
# 4. held-out 16, base and new
$T/heldout_pair.sh $BASE $NEW pair
log heldout done
# 5. 112 nominal ORE inputs
$T/ore_nominal.sh $BASE $NEW
log nominal done
# 6. the seed pools, NEW on every seed
$T/pools.sh $NEW after
log pools after done
# 7. the base on every pool seed that was not ok after the fix on some route
for f in $S/pools/after/*.tsv; do n=$(basename $f .tsv); awk -F'\t' -v n=$n '$3!="ok"{print n"\t"$1}' $f; done | sort -u > $S/pools/nonok.list
$T/pools.sh $BASE before $S/pools/nonok.list
log pools before done
