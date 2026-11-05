#!/bin/bash
# campaign.sh : every KM measurement of fix/v155-bridge-nn-term, one step
# after another, never more than two KM processes at a time.
# BASE = 1ffee4a6 (before the NN-rule), N48 = 48a1113b (the NN-rule port),
# NEW = this branch.
T=$(dirname $(readlink -f $0))
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/bridge-nn-term
BASE=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/bridge-nn-rule/bin/km-base
N48=$S/bin/km-48a; NEW=${NEW:-$S/bin/km-new}
log(){ echo "$(date +%T) $*" >> $S/campaign.log; }
cd $S; export TMPDIR=$S/tmp
log start NEW=$NEW
# 1. the seven seeds and the reductions: NEW 3 runs, 48a and base 1 run, 120 s
mkdir -p $S/sevenrun; rm -f $S/sevenrun/*.tsv
FAM_TIMEOUT=120 FAM_FORCED_TIMEOUT=120 python3 -I $T/fam_run.py $NEW $S/seven/gold $S/sevenrun/new.tsv ht_bridge,auto 3 $S/seven/*.ofn
FAM_TIMEOUT=120 FAM_FORCED_TIMEOUT=120 python3 -I $T/fam_run.py $N48 $S/seven/gold $S/sevenrun/n48.tsv ht_bridge,auto 1 $S/seven/*.ofn
FAM_TIMEOUT=120 FAM_FORCED_TIMEOUT=120 python3 -I $T/fam_run.py $BASE $S/seven/gold $S/sevenrun/base.tsv ht_bridge,auto 1 $S/seven/*.ofn
log seven done
# 2. the NN family, 2,000 seeds, three runs, both routes (caps of the NN-rule agent)
mkdir -p $S/famrun; rm -f $S/famrun/new.tsv
FAM_TIMEOUT=60 FAM_FORCED_TIMEOUT=30 python3 -I $T/fam_run.py $NEW $S/fam/gold $S/famrun/new.tsv ht_bridge,auto 3 $S/fam/seeds/*.ofn
log family done
# 3. the gold-backed seed pools, both routes
rm -rf $S/pools/after; $T/pools.sh $NEW after
log pools done
# 4. the 16 held-out inputs, 48a then NEW
rm -f $S/runs/summary.tsv
$T/heldout.sh $N48 n48; $T/heldout.sh $NEW new
log heldout done
# 5. the 112 nominal ORE design-half inputs, 48a then NEW
$T/ore_nominal.sh $N48 $NEW
log nominal done
