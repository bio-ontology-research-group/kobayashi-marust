#!/bin/bash
# usage: run_aff.sh TAG KM_BIN SET... ; runs diff_run.py on the affected files of each set
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/top-nominal-data
O=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-assets/2026-10-28-scratch/oracle
tag=$1; km=$2; shift 2
export DIFF_KM_TIMEOUT=60 DIFF_THREADS=4
R=nominals,certified_nominals,ht_general,auto
for set in "$@"; do
  case $set in
    sorts) pat=sorts_differential; gold=$S/gold_sorts ;;
    fresh2) pat=/fresh2/; gold=$S/gold_fresh2 ;;
    fresh3) pat=/fresh3/; gold=$S/gold_fresh3 ;;
  esac
  out=$S/diff-$set-$tag.tsv; rm -f $out
  python3 -I $S/diff_run.py $km $O $gold $out $R $(grep $pat $S/affected.txt)
done
echo DONE
