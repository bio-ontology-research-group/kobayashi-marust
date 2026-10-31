#!/bin/bash
# runset.sh BIN OUT.tsv TIMEOUT THREADS FILELIST [DIFF_KEEP]: diff_run.py over FILELIST in chunks of 100 (relative to r3 scratch)
B=$(readlink -f $1); OUT=$(readlink -f $2); T=$3; TH=$4; L=$(readlink -f $5); K=${6:-}
R=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/r3-unannounced
cd $R
split -l 100 $L $OUT.chunk.
for c in $OUT.chunk.*; do
  DIFF_KEEP=$K DIFF_THREADS=$TH DIFF_KM_TIMEOUT=$T python3 -I tools/diff_run.py $B oracle gold $OUT nominals $(cat $c) >> $OUT.log 2>&1
  rm -f $c
done
echo FINISHED >> $OUT.log
