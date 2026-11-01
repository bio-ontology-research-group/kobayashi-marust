#!/bin/bash
# runset.sh BIN OUT.tsv TIMEOUT ROUTES FILELIST : diff_run.py (r3-unannounced copy) over FILELIST in chunks of 100, 3 KM runs at a time, KM_THREADS=1
B=$(readlink -f $1); OUT=$(readlink -f $2); T=$3; RT=$4; L=$(readlink -f $5)
R=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/r3-unannounced
cd $R
split -l 100 $L $OUT.chunk.
for c in $OUT.chunk.*; do
  DIFF_KEEP=KM_THREADS=1 DIFF_THREADS=3 DIFF_KM_TIMEOUT=$T python3 -I tools/diff_run.py $B oracle gold $OUT $RT $(cat $c) >> $OUT.log 2>&1
  rm -f $c
done
echo FINISHED >> $OUT.log
