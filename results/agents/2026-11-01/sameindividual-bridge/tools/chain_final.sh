#!/bin/bash
# chain_final.sh: the final measurement chain for km.v7 (two streams, then the five inputs, then 10926 alone)
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/sameindividual-bridge
F=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/v150-corpus/files
RC=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/pgo-v155/km-v1.5.5-rc-pgo
L=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/v1.5.5/results/agents/2026-10-30/r3-unannounced/ore-design-nominal.txt
OT=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/v1.5.5/results/agents/2026-10-30/r3-unannounced/ore_time.sh
REL="KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1 KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 KM_THREADS=1"
K=KM_HT_DDB=1,KM_HT_NATIVE_FULL=1,KM_CACHE_CONFORMANCE=1,KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1,KM_FAST_IRI_GRAMMAR=1,KM_THREADS=1
cd $S; export TMPDIR=$S/tmp
(
  $S/tools/run1ts.sh $S/km.v7 $F/ore_ont_16315.owl $S/runs/v7full_auto_16315 KM_HT_ADMIT_SAME=1 KM_HT_AUTOMAT_REST_LINK=1 KM_HT_CONDITIONAL_FULL_LIMIT=1000000 KM_HT_STATS=1 KM_BRIDGE_PROGRESS=1
  rm -f $S/ore/times-v7.tsv; mkdir -p $S/ore
  bash $OT $S/km.v7 $L $S/ore v7 $REL
) &
(
  DIFF_KM_TIMEOUT=30 DIFF_THREADS=1 DIFF_KEEP=$K python3 -I tools/diff_run.py $S/km.v7 $S/../../agent-assets/2026-10-28-scratch/oracle $S/gold diff/v7.tsv ht_bridge,auto $(ls seeds/s*.ofn | sort -V) > diff/v7.log 2>&1
  DIFF_KM_TIMEOUT=30 DIFF_THREADS=1 DIFF_KEEP=$K python3 -I tools/diff_run.py $S/km.v7 $S/../../agent-assets/2026-10-28-scratch/oracle $S/cgold diff/chain-v7.tsv ht_bridge,auto $(ls cseeds/c*.ofn | sort -V) > diff/chain-v7.log 2>&1
  rm -f $S/ore/times-base.tsv; mkdir -p $S/ore
  bash $OT $RC $L $S/ore base $REL
) &
wait
for pair in "16315 10838" "3087 7557"; do set -- $pair
  $S/tools/run1.sh $S/km.v7 $F/ore_ont_$1.owl $S/runs/final_auto_$1 &
  $S/tools/run1.sh $S/km.v7 $F/ore_ont_$2.owl $S/runs/final_auto_$2 &
  wait
done
$S/tools/run1.sh $S/km.v7 $F/ore_ont_10926.owl $S/runs/final_auto_10926 KM_BRIDGE_MEM=1 KM_BRIDGE_PROGRESS=1
echo DONE > $S/chain_final.done
