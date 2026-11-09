#!/bin/bash
# campaign.sh BIN : the measurement campaign of results/agents/2026-11-02/bridge-self,
# strictly sequential so that at most two KM runs share the host.
# 1. the 16 held-out inputs (after), and the SELF inputs 6132/9899 before;
# 2. the SELF seed family, both routes, after and before;
# 3. the gold-backed pools of earlier agents, both routes, after and before.
T=$(dirname $(readlink -f $0)); BIN=$1
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/bridge-self
$T/heldout.sh $BIN after
for n in 6132 9899; do $T/one.sh $BIN $n before KM_BRIDGE_SAT_REFUSE_SELF=1; done
echo "=== heldout done $(date)"
$T/seeds.sh $BIN self-after
DIFF_EXTRA=KM_BRIDGE_SAT_REFUSE_SELF=1 $T/seeds.sh $BIN self-before
echo "=== self family done $(date)"
POOLS=$(ls -d $S/pools/* | tr '\n' ' ')
$T/seeds.sh $BIN pools-after ht_bridge,auto "$POOLS"
echo "=== pools after done $(date)"
DIFF_EXTRA=KM_BRIDGE_SAT_REFUSE_SELF=1 $T/seeds.sh $BIN pools-before ht_bridge,auto "$POOLS"
echo "=== pools before done $(date)"
