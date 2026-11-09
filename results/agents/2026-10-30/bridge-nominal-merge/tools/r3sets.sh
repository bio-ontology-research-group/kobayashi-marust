#!/bin/bash
# r3sets.sh BIN TAG: R3 motif sets on ht_bridge and auto against HermiT
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch
B=$1; T=$2; cd $S/bridge-nominal-merge; export TMPDIR=$PWD/tmp
D=$S/../worktrees/fix-bridge-nominal-merge/results/agents/2026-10-30/r3-unannounced
for set in tpl:20 tpl2:20 seeds:10; do n=${set%%:*}; t=${set##*:}
  DIFF_THREADS=8 DIFF_KM_TIMEOUT=$t python3 -I $D/diff_run.py $B $S/r3-unannounced/oracle $S/r3-unannounced/gold r3-$n-$T.tsv ht_bridge,auto $S/r3-unannounced/$n/*.ofn > r3-$n-$T.log 2>&1
done
echo DONE > r3-$T.done
