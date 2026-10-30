#!/bin/bash
# usage: run_1029.sh KM_BIN TAG : the 2026-10-29 rule probes and nominal-data seeds, auto route, 60 s, 3 threads
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch
T=$S/top-nominal-data
D=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/fix-fr282-dropped-rules/results/agents/2026-10-30/fr282-dropped-rules/diff_run.py
O=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-assets/2026-10-28-scratch/oracle
export DIFF_THREADS=3 DIFF_KM_TIMEOUT=60 TMPDIR=$S/fr282-dropped-rules/home-tmp
out=$S/fr282-dropped-rules/d1029-$2; mkdir -p $out
rm -f $out/*.tsv
python3 -I $D $1 $O $T/gold_rules $out/rules.tsv auto $T/rules/*.ofn
python3 -I $D $1 $O $T/gold_fresh2 $out/fresh2.tsv auto $(grep /fresh2/ $T/affected.txt)
python3 -I $D $1 $O $T/gold_fresh3 $out/fresh3.tsv auto $(grep /fresh3/ $T/affected.txt)
echo DONE
