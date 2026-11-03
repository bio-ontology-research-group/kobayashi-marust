#!/bin/bash
# campaign2.sh NEW_BIN BASE_BIN : the rest of the campaign after the pools on
# NEW_BIN: the targeted base rerun of the pools, the 16 held-out inputs, the
# 112 nominal design-half inputs, the C1 sample, the test suites.
T=$(dirname $(readlink -f $0)); NEW=$1; BASE=$2
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/cb-s974
$T/pools_before.sh $BASE; echo "=== pools before $(date)"
$T/heldout.sh $NEW after; echo "=== heldout after $(date)"
$T/heldout.sh $BASE before; echo "=== heldout before $(date)"
$T/ore_nominal.sh $BASE $NEW; echo "=== nominal $(date)"
$T/c1_run.sh $BASE $NEW; echo "=== c1 $(date)"
$T/tests.sh $S/tests; echo "=== tests $(date)"
