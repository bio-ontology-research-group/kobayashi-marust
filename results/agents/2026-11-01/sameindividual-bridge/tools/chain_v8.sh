#!/bin/bash
# chain_v8.sh: diagnostic switches with km.v8 on the family, 10926 alone, then paired ORE nominal (non-PGO base vs v8) and the 66 small SameIndividual ORE inputs
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/sameindividual-bridge
F=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/v150-corpus/files
L=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/v1.5.5/results/agents/2026-10-30/r3-unannounced/ore-design-nominal.txt
OT=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/v1.5.5/results/agents/2026-10-30/r3-unannounced/ore_time.sh
REL="KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1 KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 KM_THREADS=1"
DIAG="KM_HT_ADMIT_SAME=1 KM_HT_AUTOMAT_REST_LINK=1 KM_HT_CONDITIONAL_FULL_LIMIT=1000000"
cd $S; export TMPDIR=$S/tmp
$S/tools/run1ts.sh $S/km.v8 $F/ore_ont_16315.owl $S/runs/diag8_16315 $DIAG KM_BRIDGE_PROGRESS=1 KM_HT_STATS=1 &
$S/tools/run1ts.sh $S/km.v8 $F/ore_ont_7557.owl $S/runs/diag8_7557 $DIAG KM_BRIDGE_PROGRESS=1 KM_HT_STATS=1 &
wait
$S/tools/run1ts.sh $S/km.v8 $F/ore_ont_10926.owl $S/runs/diag8_10926 $DIAG KM_BRIDGE_PROGRESS=1 KM_HT_STATS=1 KM_BRIDGE_MEM=1
echo DIAG > $S/chain_v8.progress
rm -f $S/ore/times-v8.tsv $S/ore/times-basenp.tsv $S/ore/times-same-v8.tsv $S/ore/times-same-basenp.tsv
bash $OT $S/km.v8 $L $S/ore v8 $REL &
bash $OT $S/km.base-nopgo $L $S/ore basenp $REL &
wait
echo ORE > $S/chain_v8.progress
bash $OT $S/km.v8 $S/same-small.txt $S/ore same-v8 $REL &
bash $OT $S/km.base-nopgo $S/same-small.txt $S/ore same-basenp $REL &
wait
echo DONE > $S/chain_v8.done
