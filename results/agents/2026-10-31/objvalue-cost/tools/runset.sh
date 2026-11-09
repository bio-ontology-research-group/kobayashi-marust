#!/bin/bash
# runset.sh BIN OUT.tsv TIMEOUT THREADS FILELIST ROUTE: diff_run.py (r3-unannounced/tools) over FILELIST (paths relative to the r3 scratch) in chunks of 100
B=$(readlink -f $1); OUT=$(readlink -f $2); T=$3; TH=$4; L=$(readlink -f $5); RT=${6:-nominals}
R=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/r3-unannounced
cd $R
split -l 100 $L $OUT.chunk.
for c in $OUT.chunk.*; do
  DIFF_KEEP=KM_THREADS=1 DIFF_THREADS=$TH DIFF_KM_TIMEOUT=$T python3 -I tools/diff_run.py $B oracle gold $OUT $RT $(cat $c) >> $OUT.log 2>&1
  rm -f $c
done
echo FINISHED >> $OUT.log
