#!/bin/bash
cd "$(dirname "$0")"
./timing.sh > table5.tsv 2>&1
I=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/subset-blocking-cost/inputs
for i in 205 7499; do CPU=40 TO=1800 ./run1.sh ../bin/km-fix5 $I/ore_ont_$i.owl out/check-fix5-$i KM_HT_INCRBLOCK2_CHECK=1; done > check5.tsv 2>&1
CPU=40 TO=900 ./run1.sh ../bin/km-fix5 $I/ore_ont_205.owl out/stats-fix5-205 KM_HT_STATS=1 >> check5.tsv
