#!/bin/bash
# campaign.sh NEW_BIN BASE_BIN : the differential and timing campaign of
# results/agents/2026-11-03/cb-s974, strictly sequential (at most two KM
# processes at a time): seed pools after and before, the 16 held-out ORE
# inputs after and before, the 112 nominal design-half inputs, the C1
# regression sample, then the test suites.
T=$(dirname $(readlink -f $0)); NEW=$1; BASE=$2
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/cb-s974
$T/pools.sh $NEW after; echo "=== pools after $(date)"
$T/pools.sh $BASE before; echo "=== pools before $(date)"
$T/heldout.sh $NEW after; echo "=== heldout after $(date)"
$T/heldout.sh $BASE before; echo "=== heldout before $(date)"
$T/ore_nominal.sh $BASE $NEW; echo "=== nominal $(date)"
$T/c1_run.sh $BASE $NEW; echo "=== c1 $(date)"
$T/tests.sh $S/tests; echo "=== tests $(date)"
