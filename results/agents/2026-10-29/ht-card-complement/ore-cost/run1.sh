#!/bin/bash
# run1.sh BIN FILE TAG -> prints: route secs status md5
bin=$1; f=$2; tag=$3; D=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/ht-card-complement/ore/out
mkdir -p $D; b=$(basename $f .owl)
env -u KM_ROUTE $(env | grep -o '^KM_[A-Z0-9_]*' | sed 's/^/-u /') KM_ROUTE=auto KM_TIMING=1 \
  /usr/bin/time -f "%e" -o $D/$b.$tag.time taskset -c 0-3 timeout 300 $bin classify --lines $f > $D/$b.$tag.out 2> $D/$b.$tag.err
rc=$?
route=$(grep -o 'frontend done @ [0-9.]*s route=[a-z_0-9]*' $D/$b.$tag.err | head -1 | sed 's/.*route=//')
secs=$(tail -1 $D/$b.$tag.time)
md5=$(grep -E '^(SUB|UNSAT|CONSISTENT)' $D/$b.$tag.out | sort | md5sum | cut -c1-12)
n=$(grep -cE '^(SUB|UNSAT)' $D/$b.$tag.out)
echo "$b $tag ${route:-?} $secs rc=$rc lines=$n $md5"
