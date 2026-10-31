#!/bin/bash
# chain2.sh: before (km.before = 0e1bd99a) and after (km.after = merged branch) on every seed set, then the 112 ORE nominal inputs
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch
cd $S/bridge-nominal-merge; export TMPDIR=$PWD/tmp
for B in before after; do
  DIFF_KM_TIMEOUT=30 DIFF_THREADS=8 python3 -I diff_run.py $PWD/km.$B $S/../agent-assets/2026-10-28-scratch/oracle $PWD/gold gen-$B.tsv ht_bridge,auto seeds/g*.ofn > gen-$B.log 2>&1
done
for B in before after; do ./r3sets.sh $PWD/km.$B $B; done
for B in before after; do ./alc.sh $PWD/km.$B $B > alc-$B.log 2>&1; done
echo DONE > chain2.done
O=$S/../worktrees/fix-bridge-nominal-merge/results/agents/2026-10-30/r3-unannounced
L=$O/ore-design-nominal.txt
rm -f ore/times-before.tsv ore/times-after.tsv; mkdir -p ore
bash $O/ore_time.sh $PWD/km.before $L $PWD/ore before &
bash $O/ore_time.sh $PWD/km.after $L $PWD/ore after &
wait
echo DONE > ore.done
