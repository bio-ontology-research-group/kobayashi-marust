#!/bin/bash
# poor man's profiler: pmp.sh PID N INTERVAL
P=$1; N=$2; I=$3
for i in $(seq $N); do gdb -p $P -batch -ex "bt 30" 2>/dev/null | grep -E "^#" | sed -E 's/0x[0-9a-f]+ in //; s/ \(.*//' | awk '{print $2}' | head -12 | paste -sd';' ; sleep $I; done
