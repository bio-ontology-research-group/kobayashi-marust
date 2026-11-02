#!/bin/bash
# campaign4.sh BIN : final sequence on the final binary, at most two KM runs.
T=$(dirname $(readlink -f $0)); BIN=$1
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/bridge-self
$T/seeds.sh $BIN self-after
echo "=== self after done $(date)"
$T/one.sh $BIN 12128 final
CAP=400 $T/one.sh $BIN 12128 final400
$T/one.sh $BIN 6132 final & $T/one.sh $BIN 9899 final & wait
echo "=== heldout self done $(date)"
$T/itests.sh $S/tests-final
echo "=== tests done $(date)"
POOLS=$(ls -d $S/pools/* | tr '\n' ' ')
RESUME=1 $T/seeds.sh $BIN pools-after ht_bridge,auto "$POOLS"
echo "=== pools after done $(date)"
