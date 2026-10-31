#!/bin/bash
# alc.sh BIN TAG: the 2026-10-29 bridge seed sets (700 ALCHIQ + fresh 300), auto and ht_bridge
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work
B=$1; T=$2; cd $S/agent-scratch/bridge-nominal-merge; export TMPDIR=$PWD/tmp
E=$S/worktrees/fix-bridge-nominal-merge/results/agents/2026-10-29/cb-inverse-top/eval.py
export GEN=$S/worktrees/fix-bridge-nominal-merge/results/agents/2026-10-28/generators/gen_alc.py ORACLE=$S/agent-assets/2026-10-28-scratch/oracle J=6
SQ=$S/agent-assets/2026-10-28-scratch/sq SEEDS=$S/agent-assets/2026-10-28-scratch/bridge/seeds GOLD=$S/agent-assets/2026-10-28-scratch/bridge/gold python3 -I $E $B 1 701 alc/s700_${T}_auto.txt
SQ=$S/agent-assets/2026-10-28-scratch/sq SEEDS=$S/agent-assets/2026-10-28-scratch/bridge/seeds GOLD=$S/agent-assets/2026-10-28-scratch/bridge/gold python3 -I $E $B 1 701 alc/s700_${T}_htb.txt KM_ROUTE=ht_bridge
SQ= SEEDS=$PWD/alc/fresh/seeds GOLD=$PWD/alc/fresh/gold python3 -I $E $B 1000 1300 alc/f300_${T}_auto.txt
SQ= SEEDS=$PWD/alc/fresh/seeds GOLD=$PWD/alc/fresh/gold python3 -I $E $B 1000 1300 alc/f300_${T}_htb.txt KM_ROUTE=ht_bridge
for f in alc/*_${T}_*.txt; do echo "$(basename $f): $(awk '{print $2}' $f | sed 's/(.*//' | sort | uniq -c | tr '\n' ' ')"; done > alc/counts-$T.txt
