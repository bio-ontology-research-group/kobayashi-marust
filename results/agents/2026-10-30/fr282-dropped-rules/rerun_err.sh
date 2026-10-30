#!/bin/bash
# usage: rerun_err.sh KM_BIN IN.tsv OUT.tsv : rerun the ERR rows of IN with one thread, write a merged OUT
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/fr282-dropped-rules
export DIFF_THREADS=1 DIFF_KM_TIMEOUT=60 TMPDIR=$S/home-tmp
F=$(awk -F'\t' '$3=="ERR"{print $1}' $2)
rm -f $3.err-rerun
[ -n "$F" ] && python3 -I /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/fix-fr282-dropped-rules/results/agents/2026-10-30/fr282-dropped-rules/diff_run.py $1 /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-assets/2026-10-28-scratch/oracle $S/seeds/gold $3.err-rerun auto $F
touch $3.err-rerun
if [ ! -s $3.err-rerun ]; then cp $2 $3; exit 0; fi
awk -F'\t' 'NR==FNR{r[$1]=$0;next} ($1 in r){print r[$1];next} {print}' $3.err-rerun $2 > $3
