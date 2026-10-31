#!/bin/bash
# usage: drive.sh <tag> [pools...]; differential runs against cached HermiT answers, 3 KM runs at a time, one CPU each
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/forced-nominal-data-misses
W=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work
DR=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/fix-forced-nominal-data-misses/results/agents/2026-10-30/data-values-3/scripts/diff_run.py
OR=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/data-values/oracle
tag=$1; shift
KM=$S/tools/one-$tag
export DIFF_THREADS=3 DIFF_KEEP=KM_THREADS=1 TMPDIR=$S/tmp/$tag; mkdir -p $TMPDIR $S/runs
for pool in "$@"; do
  out=$S/runs/$pool-$tag.tsv; rm -f $out
  case $pool in
    probes) DIFF_KM_TIMEOUT=60 python3 -I $DR $KM $OR /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/fix-forced-nominal-data-misses/results/agents/2026-10-30/data-values/probes/gold $out auto,certified_nominals,nominals $W/agent-scratch/data-values/probes/gen/*.ofn ;;
    fixtures) DIFF_KM_TIMEOUT=60 python3 -I $DR $KM $OR $S/gold-fixtures $out auto,certified_nominals,nominals $S/fixtures/*.ofn ;;
    tnd-sorts|tnd-fresh2|tnd-fresh3)
      set=${pool#tnd-}; T=$W/agent-scratch/top-nominal-data
      case $set in sorts) pat=sorts_differential ;; *) pat=/$set/ ;; esac
      DIFF_KM_TIMEOUT=60 python3 -I $DR $KM $W/agent-assets/2026-10-28-scratch/oracle $T/gold_$set $out nominals,certified_nominals,auto $(grep $pat $W/agent-scratch/data-values/diff/tnd-files.txt | sed 's#/worktrees/fix-native-data-values/#/worktrees/fix-forced-nominal-data-misses/#') ;;
    nomdata-auto) DIFF_KM_TIMEOUT=60 python3 -I $DR $KM $OR $W/agent-scratch/nominal-coverage/gold $out auto $W/agent-scratch/nominal-coverage/seeds/m2*.ofn ;;
    nomdata-forced) DIFF_KM_TIMEOUT=30 python3 -I $DR $KM $OR $W/agent-scratch/nominal-coverage/gold $out nominals,certified_nominals $W/agent-scratch/nominal-coverage/seeds/m2*.ofn ;;
    r3data-auto) DIFF_KM_TIMEOUT=30 python3 -I $DR $KM $OR $W/agent-scratch/r3-unannounced/gold $out auto $(grep -l Data $W/agent-scratch/r3-unannounced/*/*.ofn) ;;
    r1600-auto) DIFF_KM_TIMEOUT=30 python3 -I $DR $KM $OR $W/agent-scratch/nominal-r1600/frseeds/gold $out auto $(grep -l Data $W/agent-scratch/nominal-r1600/frseeds/ofn/*.ofn) ;;
  esac
  echo "$pool done $(cut -f3 $out | sort | uniq -c | tr '\n' ' ')"
done
rm -rf $TMPDIR
