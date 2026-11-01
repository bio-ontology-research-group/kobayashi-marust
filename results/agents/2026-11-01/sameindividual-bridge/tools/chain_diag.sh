#!/bin/bash
# chain_diag.sh: the three diagnostic switches on the family, two at a time, then a paired ORE nominal run (non-PGO base vs v7)
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/sameindividual-bridge
F=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/v150-corpus/files
L=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/v1.5.5/results/agents/2026-10-30/r3-unannounced/ore-design-nominal.txt
OT=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/v1.5.5/results/agents/2026-10-30/r3-unannounced/ore_time.sh
REL="KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1 KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 KM_THREADS=1"
DIAG="KM_HT_ADMIT_SAME=1 KM_HT_AUTOMAT_REST_LINK=1 KM_HT_CONDITIONAL_FULL_LIMIT=1000000"
cd $S; export TMPDIR=$S/tmp
for pair in "10838 3087" "7557 15846"; do set -- $pair
  $S/tools/run1ts.sh $S/km.v7 $F/ore_ont_$1.owl $S/runs/diag_$1 $DIAG KM_BRIDGE_PROGRESS=1 KM_HT_STATS=1 &
  $S/tools/run1ts.sh $S/km.v7 $F/ore_ont_$2.owl $S/runs/diag_$2 $DIAG KM_BRIDGE_PROGRESS=1 KM_HT_STATS=1 &
  wait
done
$S/tools/run1.sh $S/km.v7 $F/ore_ont_16315.owl $S/runs/diag_16315 $DIAG
echo DIAG > $S/chain_diag.progress
rm -f $S/ore/times-v7b.tsv $S/ore/times-basenp.tsv
bash $OT $S/km.v7 $L $S/ore v7b $REL &
bash $OT $S/km.base-nopgo $L $S/ore basenp $REL &
wait
echo DONE > $S/chain_diag.done
