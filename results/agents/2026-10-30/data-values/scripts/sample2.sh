#!/bin/bash
# usage: sample2.sh <binary-path> <outfile> <n> <interval>; top frames of every thread of the busiest process
bin=$1; out=$2; n=${3:-20}; iv=${4:-1}
: > $out
for i in $(seq $n); do
  pid=$(ps -eo pid,pcpu,args --sort=-pcpu | awk -v b="$bin" '$3==b {print $1; exit}')
  [ -z "$pid" ] && { sleep $iv; continue; }
  timeout 30 gdb -p $pid -batch -ex "thread apply all bt 12" 2>/dev/null | grep -E "^(Thread|#)" | sed -E 's/^(#[0-9]+) +(0x[0-9a-f]+ in )?/\1 /; s/ \(.*//' >> $out
  echo "=== end $i" >> $out
  sleep $iv
done
