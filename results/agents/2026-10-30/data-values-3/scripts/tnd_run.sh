#!/bin/bash
# usage: tnd_run.sh <tag> <km>; reruns the 2026-10-29 top-nominal-data affected set (87 files, 4 routes, 60 s)
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/data-values-3
T=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/top-nominal-data
O=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-assets/2026-10-28-scratch/oracle
tag=$1; km=$2
export DIFF_KM_TIMEOUT=60 DIFF_THREADS=${DIFF_THREADS:-4} TMPDIR=$S/tnd/tmp-$tag; mkdir -p $TMPDIR
R=nominals,certified_nominals,ht_general,auto
for set in sorts fresh2 fresh3; do
  case $set in sorts) pat=sorts_differential; gold=$T/gold_sorts ;; fresh2) pat=/fresh2/; gold=$T/gold_fresh2 ;; fresh3) pat=/fresh3/; gold=$T/gold_fresh3 ;; esac
  out=$S/tnd/diff-$set-$tag.tsv; rm -f $out
  python3 -I $T/diff_run.py $km $O $gold $out $R $(grep $pat /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/data-values/diff/tnd-files.txt)
done
rm -rf $TMPDIR
echo DONE
