#!/bin/bash
# usage: run_diff.sh KM_BIN OUT.tsv [DIFF_KEEP]
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/fr282-dropped-rules
export DIFF_THREADS=3 DIFF_KM_TIMEOUT=60 TMPDIR=$S/home-tmp DIFF_KEEP=${3:-}
F=$(ls $S/seeds/ofn/*.ofn | sort -V)
rm -f $2
python3 -I /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/fix-fr282-dropped-rules/results/agents/2026-10-30/fr282-dropped-rules/diff_run.py $1 /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-assets/2026-10-28-scratch/oracle $S/seeds/gold $2 auto $F
