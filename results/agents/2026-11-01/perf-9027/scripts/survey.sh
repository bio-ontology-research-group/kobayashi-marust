#!/bin/bash
# survey.sh OUT FILE...: on auto, record whether the bridge saw singletons and proved them inert.
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/perf-9027
OUT=$1; shift
export TMPDIR=$S/tmp/survey KM_THREADS=1 KM_HT_STATS=1; mkdir -p $TMPDIR
: > $OUT
for f in "$@"; do
  line=$(timeout -s KILL 30 $S/tools/one-perf classify --lines $f 2>&1 >/dev/null | grep -o 'singleton-inert\] singletons=[0-9]* inert=[a-z]*' | head -1)
  echo -e "$(basename $f)\t${line:-none}" >> $OUT
done
