#!/bin/bash
# ore.sh: the 112 nominal ORE inputs, km.after and km.fix1 side by side, KM_THREADS=1, 300 s
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/bridge-merge-edges
O=$S/../../worktrees/fix-bridge-merge-edges/results/agents/2026-10-30/r3-unannounced
cd $S; export TMPDIR=$S/tmp; rm -f ore/times-after.tsv ore/times-fix1.tsv
bash $O/ore_time.sh $S/km.after $O/ore-design-nominal.txt $S/ore after KM_THREADS=1 &
bash $O/ore_time.sh $S/km.fix1 $O/ore-design-nominal.txt $S/ore fix1 KM_THREADS=1 &
wait; echo DONE > ore.done
