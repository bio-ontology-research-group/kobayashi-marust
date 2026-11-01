#!/bin/bash
# drive.sh POOL...: differential runs of km.pgo.fix2 (audit on) against cached HermiT answers, 3 KM runs at a time.
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/perf-9027
W=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work
F=$W/agent-scratch/forced-nominal-data-misses
WT=$W/worktrees/fix-perf-9027
DR=$WT/results/agents/2026-10-30/data-values-3/scripts/diff_run.py
OR=$W/agent-scratch/data-values/oracle
KM=$S/tools/one-perf
export DIFF_THREADS=3 DIFF_KEEP=KM_THREADS=1,KM_HT_SINGLETON_INERT_AUDIT=1 TMPDIR=$S/tmp/diff; mkdir -p $TMPDIR $S/runs
for pool in "$@"; do
  out=$S/runs/$pool.tsv; : > $out
  case $pool in
    probes) DIFF_KM_TIMEOUT=60 python3 -I $DR $KM $OR $WT/results/agents/2026-10-30/data-values/probes/gold $out auto,certified_nominals,nominals $W/agent-scratch/data-values/probes/gen/*.ofn ;;
    fixtures) DIFF_KM_TIMEOUT=60 python3 -I $DR $KM $OR $F/gold-fixtures $out auto,certified_nominals,nominals $F/fixtures/*.ofn ;;
    tnd-sorts|tnd-fresh2|tnd-fresh3)
      set=${pool#tnd-}; T=$W/agent-scratch/top-nominal-data
      case $set in sorts) pat=sorts_differential ;; *) pat=/$set/ ;; esac
      DIFF_KM_TIMEOUT=60 python3 -I $DR $KM $W/agent-assets/2026-10-28-scratch/oracle $T/gold_$set $out nominals,certified_nominals,auto $(grep $pat $S/tnd-files.txt) ;;
    nomdata-auto) DIFF_KM_TIMEOUT=60 python3 -I $DR $KM $OR $W/agent-scratch/nominal-coverage/gold $out auto $W/agent-scratch/nominal-coverage/seeds/m2*.ofn ;;
    r3data-auto) DIFF_KM_TIMEOUT=30 python3 -I $DR $KM $OR $W/agent-scratch/r3-unannounced/gold $out auto $(grep -l Data $W/agent-scratch/r3-unannounced/*/*.ofn) ;;
    r1600-auto) DIFF_KM_TIMEOUT=30 python3 -I $DR $KM $OR $W/agent-scratch/nominal-r1600/frseeds/gold $out auto $(grep -l Data $W/agent-scratch/nominal-r1600/frseeds/ofn/*.ofn) ;;
  esac
  echo "$pool done $(cut -f3 $out | sort | uniq -c | tr '\n' ' ')"
done
