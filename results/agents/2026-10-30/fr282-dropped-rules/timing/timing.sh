#!/bin/bash
# One run at a time on one core, routing policy v153 (the release default),
# 7278 and 3726, three binaries. usage: timing.sh OUTDIR BIN...
out=$1; shift; mkdir -p $out/runs
R=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/fix-fr282-dropped-rules/results/agents/2026-10-30/rules-worker-cost/timing/run1.sh
IN=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/subset-blocking-cost/inputs
for o in 7278 3726; do
  for b in "$@"; do
    line=$(CPU=${CPU:-44} TO=900 TMPDIR=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/fr282-dropped-rules/home-tmp $R $b $IN/ore_ont_$o.owl $out/runs/$(basename $b)-$o)
    md5=$(md5sum < $out/runs/$(basename $b)-$o.out | cut -c1-12)
    echo -e "$line\t$md5" | tee -a $out/table.tsv
  done
done
