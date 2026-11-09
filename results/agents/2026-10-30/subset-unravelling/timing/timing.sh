#!/bin/bash
# One-core timing of 205 and 7499 (card arm route), base and fixed binary, alternating.
cd "$(dirname "$0")"
I=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/subset-blocking-cost/inputs
B=${B:-km-fix3}
for rep in 1 2; do
for i in 205 7499; do
  for b in km-base $B; do
    CPU=${CPU:-40} TO=900 ./run1.sh ../bin/$b $I/ore_ont_$i.owl out/$b-$i-r$rep
  done
done
done
