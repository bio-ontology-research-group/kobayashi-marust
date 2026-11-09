#!/bin/bash
# reruns.sh : 9577 (held-out, new 78.9 s vs base 64.3 s in the paired run)
# three times base and new side by side; the two borderline family seeds
# refl1250 and refl1477 (automatic route) three times on each binary; then
# the base on every pool seed that was not ok after the fix.
T=$(dirname $(readlink -f $0)); S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/bridge-reflexive
for i in 1 2 3; do $T/one.sh $S/bin/km-base 9577 base-r$i & $T/one.sh $S/bin/km-v3 9577 new-r$i & wait; done
cd $S; mkdir -p $S/famrun/border
for b in base v3; do FAM_TIMEOUT=60 python3 -I $T/fam_run.py $S/bin/km-$b $S/fam/gold $S/famrun/border/$b.tsv auto 3 $S/fam/seeds/refl1250.ofn $S/fam/seeds/refl1477.ofn; done
echo reruns done >> $S/campaign.log
$T/pools.sh $S/bin/km-base before $S/pools/nonok.list
echo pools before done >> $S/campaign.log
