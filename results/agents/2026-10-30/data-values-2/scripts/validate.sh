#!/bin/bash
# usage: validate.sh <tag> <km>; lean probes, data probes, nominal-data seeds
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/data-values-2
W=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/fix-data-values-2
tag=$1; km=$2; cd $S
P=$W/results/agents/2026-10-30/lean-data-values
DIFF_THREADS=4 DIFF_KM_TIMEOUT=60 DIFF_KEEP=${DIFF_KEEP:-} python3 -I $P/scripts/diff_run.py $km ../data-values/oracle $P/gold diff/lean-probes-$tag.tsv auto,certified_nominals,nominals $P/probes/*.ofn > /dev/null 2>&1
DIFF_THREADS=4 DIFF_KM_TIMEOUT=120 python3 -I $W/results/agents/2026-10-30/data-values/scripts/diff_run.py $km ../data-values/oracle ../data-values/probes/gold diff/probes-$tag.tsv auto,certified_nominals,nominals ../data-values/probes/gen/*.ofn > /dev/null 2>&1
DIFF_THREADS=4 bin/tnd_run.sh $tag $km > logs/tnd-$tag.log 2>&1
echo DONE
