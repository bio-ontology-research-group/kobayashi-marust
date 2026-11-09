#!/bin/bash
# pools_after.sh BIN : the gold-backed pools of earlier agents, after column,
# resuming, one KM run at a time (runs beside the test suite).
T=$(dirname $(readlink -f $0)); BIN=$1
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/bridge-self
POOLS=$(ls -d $S/pools/* | tr '\n' ' ')
DIFF_THREADS=1 RESUME=1 $T/seeds.sh $BIN pools-after ht_bridge,auto "$POOLS"
echo "=== pools after (parallel) done $(date)"
