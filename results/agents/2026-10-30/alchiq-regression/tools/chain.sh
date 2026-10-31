#!/bin/bash
# chain.sh BIN TAG: ALCHIQ 700+300 (eval.py, 60 s), gen_merge 2000 (30 s), R3 tpl/tpl2 (20 s), 4000 random R3 seeds (10 s); 3 parallel, KM_THREADS=1
W=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work
S=$W/agent-scratch; R=$W/worktrees/fix-alchiq-regression/results/agents
B=$1; T=$2; cd $S/alchiq-regression; export TMPDIR=$PWD/tmp; mkdir -p alc out
E=$R/2026-10-29/cb-inverse-top/eval.py; D=$R/2026-10-30/r3-unannounced/diff_run.py
export GEN=$R/2026-10-28/generators/gen_alc.py ORACLE=$W/agent-assets/2026-10-28-scratch/oracle J=3
A=$W/agent-assets/2026-10-28-scratch
SQ=$A/sq SEEDS=$A/bridge/seeds GOLD=$A/bridge/gold python3 -I $E $B 1 701 alc/s700_${T}_auto.txt KM_THREADS=1
SQ= SEEDS=$S/bridge-nominal-merge/alc/fresh/seeds GOLD=$S/bridge-nominal-merge/alc/fresh/gold python3 -I $E $B 1000 1300 alc/f300_${T}_auto.txt KM_THREADS=1
SQ=$A/sq SEEDS=$A/bridge/seeds GOLD=$A/bridge/gold python3 -I $E $B 1 701 alc/s700_${T}_htb.txt KM_ROUTE=ht_bridge KM_THREADS=1
SQ= SEEDS=$S/bridge-nominal-merge/alc/fresh/seeds GOLD=$S/bridge-nominal-merge/alc/fresh/gold python3 -I $E $B 1000 1300 alc/f300_${T}_htb.txt KM_ROUTE=ht_bridge KM_THREADS=1
for f in alc/*_${T}_*.txt; do echo "$(basename $f): $(awk '{print $2}' $f | sed 's/(.*//' | sort | uniq -c | tr '\n' ' ')"; done > alc/counts-$T.txt
export DIFF_KEEP=KM_THREADS=1 DIFF_THREADS=3
DIFF_KM_TIMEOUT=30 python3 -I $D $B $ORACLE $S/bridge-nominal-merge/gold out/gen-$T.tsv ht_bridge,auto $S/bridge-nominal-merge/seeds/g*.ofn > out/gen-$T.log 2>&1
for set in tpl:20 tpl2:20 seeds:10; do n=${set%%:*}; t=${set##*:}
  DIFF_KM_TIMEOUT=$t python3 -I $D $B $S/r3-unannounced/oracle $S/r3-unannounced/gold out/r3-$n-$T.tsv ht_bridge,auto $S/r3-unannounced/$n/*.ofn > out/r3-$n-$T.log 2>&1
done
echo DONE > chain-$T.done
