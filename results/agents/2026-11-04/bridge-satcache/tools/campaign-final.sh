#!/bin/bash
# campaign-final.sh : the third agent's measurements of the final binary
# (km-final: 2cba8fbd plus the restored SELF gate and the cached legacy-arm
# accessor), one step after another, never more than two KM processes at a
# time. BASE = 48a1113b. Steps can be skipped with STEP=n.
T=$(dirname $(readlink -f $0))
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/bridge-satcache
BASE=$S/bin/km-base; NEW=${NEW:-$S/bin/km-final}
log(){ echo "$(date +%T) $*" >> $S/campaign-final.log; }
cd $S
STEP=${STEP:-0}
log start NEW=$NEW STEP=$STEP
if [ $STEP -le 0 ]; then
# 0. library and integration suites (clean environment, one process)
rm -rf $S/tests-final; $T/tests.sh $S/tests-final
log tests done
fi
if [ $STEP -le 1 ]; then
# 1. reductions and seeds, the SELF fixtures and the bridge_reflexive
# fixtures: 20 runs, both routes
rm -f $S/red20-final.tsv $S/self20-final.tsv $S/refl20-final.tsv
FAM_FORCED_TIMEOUT=60 python3 -I $T/fam_run.py $NEW $S/gold $S/red20-final.tsv ht_bridge,auto 20 $S/red/*.ofn
FAM_FORCED_TIMEOUT=60 python3 -I $T/fam_run.py $NEW $S/selffix/gold $S/self20-final.tsv ht_bridge,auto 20 $S/selffix/*.ofn
FAM_FORCED_TIMEOUT=60 python3 -I $T/fam_run.py $NEW $S/reflfix/gold $S/refl20-final.tsv ht_bridge,auto 20 $S/reflfix/*.ofn
log red20 done
fi
if [ $STEP -le 2 ]; then
# 2. the sibling family: run 1 on every seed, runs 2 and 3 on every
# seed-route that answered in run 1 (as campaign.sh); the base run is reused
export FAM_TIMEOUT=30 FAM_FORCED_TIMEOUT=20
rm -f $S/famrun/final1.tsv $S/famrun/final23-*.tsv
python3 -I $T/fam_run.py $NEW $S/famgold $S/famrun/final1.tsv ht_bridge,auto 1 $S/fam/*.ofn
log family run 1 done
for r in ht_bridge auto; do
  files=$(awk -F'\t' -v r=$r '$2==r && $4!="TIMEOUT" && $4!="NOGOLD" {print $1}' $S/famrun/final1.tsv)
  python3 -I $T/fam_run.py $NEW $S/famgold $S/famrun/final23-$r.tsv $r 2 $files
done
unset FAM_TIMEOUT FAM_FORCED_TIMEOUT
log family runs 2-3 done
fi
if [ $STEP -le 3 ]; then
# 3. held-out 16, paired with the base
$T/heldout_pair.sh $BASE $NEW final
log heldout done
fi
if [ $STEP -le 4 ]; then
# 4. 112 nominal ORE inputs, paired with the base
$T/ore_nominal_pair.sh $BASE $NEW
log nominal done
fi
if [ $STEP -le 5 ]; then
# 5. the seed pools, NEW on every seed; the base on every pool seed that was
# not ok after the fix on some route
rm -rf $S/pools/after $S/pools/before
$T/pools.sh $NEW after
log pools after done
for f in $S/pools/after/*.tsv; do n=$(basename $f .tsv); awk -F'\t' -v n=$n '$3!="ok"{print n"\t"$1}' $f; done | sort -u > $S/pools/nonok.list
$T/pools.sh $BASE before $S/pools/nonok.list
log pools before done
fi
log end
