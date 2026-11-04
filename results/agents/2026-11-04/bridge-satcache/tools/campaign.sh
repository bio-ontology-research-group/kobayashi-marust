#!/bin/bash
# campaign.sh : every KM measurement of this branch, one step after another,
# never more than two KM processes at a time (adapted from
# results/agents/2026-11-04/bridge-nn-rule/tools/campaign.sh).
# BASE = 48a1113b, NEW = the fix (LTO release builds of both).
T=$(dirname $(readlink -f $0))
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/bridge-satcache
BASE=$S/bin/km-base; NEW=${NEW:-$S/bin/km-new}
log(){ echo "$(date +%T) $*" >> $S/campaign.log; }
cd $S
log start NEW=$NEW
STEP=${STEP:-1}
if [ $STEP -le 1 ]; then
# 1. ore_ont_12128 alone, three alternating pairs (this cache's main input)
for i in 1 2 3; do $T/one.sh $BASE 12128 base-$i; $T/one.sh $NEW 12128 new-$i; done
log 12128 done
# 2. the reductions and seeds, 20 runs, both routes; the SELF fixtures 20 runs
rm -f $S/red20-new.tsv $S/self20-new.tsv
FAM_FORCED_TIMEOUT=60 python3 -I $T/fam_run.py $NEW $S/gold $S/red20-new.tsv ht_bridge,auto 20 $S/red/*.ofn
FAM_FORCED_TIMEOUT=60 python3 -I $T/fam_run.py $NEW $S/selffix/gold $S/self20-new.tsv ht_bridge,auto 20 $S/selffix/*.ofn
FAM_FORCED_TIMEOUT=60 python3 -I $T/fam_run.py $BASE $S/gold $S/red1-base.tsv ht_bridge,auto 1 $S/red/*.ofn
log red20 done
fi
# 3. the sibling family (30 s automatic, 20 s ht_bridge): one run on NEW and
# BASE; runs 2 and 3 on NEW for every seed-route that answered in run 1
# (about one seed in ten times out on both binaries in every run).
mkdir -p $S/famrun
export FAM_TIMEOUT=30 FAM_FORCED_TIMEOUT=20
rm -f $S/famrun/new1.tsv $S/famrun/base.tsv $S/famrun/new23-*.tsv
python3 -I $T/fam_run.py $NEW $S/famgold $S/famrun/new1.tsv ht_bridge,auto 1 $S/fam/*.ofn
log family new run 1 done
python3 -I $T/fam_run.py $BASE $S/famgold $S/famrun/base.tsv ht_bridge,auto 1 $S/fam/*.ofn
log family base done
for r in ht_bridge auto; do
  files=$(awk -F'	' -v r=$r '$2==r && $4!="TIMEOUT" && $4!="NOGOLD" {print $1}' $S/famrun/new1.tsv)
  python3 -I $T/fam_run.py $NEW $S/famgold $S/famrun/new23-$r.tsv $r 2 $files
done
unset FAM_TIMEOUT FAM_FORCED_TIMEOUT
log family new runs 2-3 done
# 4. held-out 16, base and new
$T/heldout.sh $BASE base; $T/heldout.sh $NEW new
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
