#!/bin/bash
# campaign2.sh BIN : the seed phases of campaign.sh (sequential, two KM runs).
T=$(dirname $(readlink -f $0)); BIN=$1
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/bridge-self
$T/seeds.sh $BIN self-after
DIFF_EXTRA=KM_BRIDGE_SAT_REFUSE_SELF=1 $T/seeds.sh $BIN self-before
echo "=== self family done $(date)"
POOLS=$(ls -d $S/pools/* | tr '\n' ' ')
$T/seeds.sh $BIN pools-after ht_bridge,auto "$POOLS"
echo "=== pools after done $(date)"
DIFF_EXTRA=KM_BRIDGE_SAT_REFUSE_SELF=1 $T/seeds.sh $BIN pools-before ht_bridge,auto "$POOLS"
echo "=== pools before done $(date)"
