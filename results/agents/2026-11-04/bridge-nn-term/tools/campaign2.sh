#!/bin/bash
# campaign2.sh : every KM measurement of the continuation (binary km-c886,
# the code of c886e3f9), one step after another, never more than two KM
# processes at a time. BASE = 1ffee4a6 (before the NN-rule), N48 = 48a1113b
# (the NN-rule port, the branch base), NEW = km-c886.
T=$(dirname $(readlink -f $0))
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/bridge-nn-term
BASE=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/bridge-nn-rule/bin/km-base
N48=$S/bin/km-48a; NEW=${NEW:-$S/bin/km-c886}
log(){ echo "$(date +%T) $*" >> $S/campaign2.log; }
cd $S; export TMPDIR=$S/tmp
log start NEW=$NEW
# 1. target seeds and reductions: NEW 20 runs per route, base and 48a 1 run, 120 s
mkdir -p $S/target/run; rm -f $S/target/run/*.tsv
FAM_TIMEOUT=120 FAM_FORCED_TIMEOUT=120 python3 -I $T/fam_run.py $NEW $S/target/gold $S/target/run/new.tsv ht_bridge,auto 20 $S/target/seeds/*.ofn
log target new done
FAM_TIMEOUT=120 FAM_FORCED_TIMEOUT=120 python3 -I $T/fam_run.py $BASE $S/target/gold $S/target/run/base.tsv ht_bridge,auto 1 $S/target/seeds/*.ofn
FAM_TIMEOUT=120 FAM_FORCED_TIMEOUT=120 python3 -I $T/fam_run.py $N48 $S/target/gold $S/target/run/n48.tsv ht_bridge,auto 1 $S/target/seeds/*.ofn
log target base 48a done
# 2. the NN family, 2,000 seeds, three runs, both routes (caps of the NN-rule agent)
rm -f $S/famrun/c886.tsv
FAM_TIMEOUT=60 FAM_FORCED_TIMEOUT=30 python3 -I $T/fam_run.py $NEW $S/fam/gold $S/famrun/c886.tsv ht_bridge,auto 3 $S/fam/seeds/*.ofn
log family done
# 3. the 16 held-out inputs, 48a and NEW side by side per input (same load)
rm -f $S/runs/summary.tsv
for n in 4903 11647 4796 3917 11378 12191 9151 9577 6132 9899 16315 10838 3087 7557 10926 12128; do
  $T/one.sh $N48 $n n48 & $T/one.sh $NEW $n c886 & wait
done
log heldout done
# 4. the 112 nominal ORE design-half inputs, 48a then NEW, one at a time
$T/ore_nominal.sh $N48 $NEW
log nominal done
# 5. the gold-backed seed pools, both routes (48a = the bridge-nn-rule agent's
#    "after" run of the byte-identical binary; the nn-rule reductions pool,
#    which that run lacks, also on 48a)
rm -rf $S/pools/c886; $T/pools.sh $NEW c886
printf 'bridge-nn-rule-red\t%s\n' $(ls /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/bridge-nn-rule/red/*.ofn) > $S/pools/nnred.list
rm -rf $S/pools/n48red; $T/pools.sh $N48 n48red $S/pools/nnred.list
log pools done
