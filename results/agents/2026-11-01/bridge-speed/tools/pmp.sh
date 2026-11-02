#!/bin/bash
# poor man's profiler: pmp.sh PID NSAMPLES INTERVAL OUT
PID=$1; N=$2; I=$3; OUT=$4
for i in $(seq $N); do
  gdb -p $PID -batch -ex "thread apply all bt 40" 2>/dev/null | grep '^#' >> $OUT
  echo "----" >> $OUT
  sleep $I
done
