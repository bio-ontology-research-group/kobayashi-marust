#!/bin/bash
# One run at a time on one core (CPU), both routing policies, three binaries.
# usage: timing.sh OUTDIR
out=$1; mkdir -p $out/runs
R=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/fix-rules-worker-cost/results/agents/2026-10-30/rules-worker-cost/timing/run1.sh
for pol in v153 general; do
 for o in 7278 3726 7499 205 10019 12107 5303; do
  for b in /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/rules-worker-cost/../subset-blocking-cost/km-v153-pgo /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/rules-worker-cost/../subset-blocking-cost/km-v154-pgo /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/rules-worker-cost/km-fix; do
   line=$(CPU=${CPU:-44} TO=900 $R $b /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/rules-worker-cost/../subset-blocking-cost/inputs/ore_ont_$o.owl $out/runs/$(basename $b)-$pol-$o KM_ROUTING_POLICY=$pol)
   md5=$(md5sum < $out/runs/$(basename $b)-$pol-$o.out | cut -c1-12)
   echo -e "$pol\t$line\t$md5" | tee -a $out/table.tsv
  done
 done
done
