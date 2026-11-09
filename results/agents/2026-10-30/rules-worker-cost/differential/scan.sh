#!/bin/bash
# usage: scan.sh BIN FILE -> file, exit, released?, rules-worker?
f=$2
env -i PATH=$PATH HOME=$HOME TMPDIR=$HOME/tmp KM_TIMING=1 timeout 60 $1 classify --lines $f > /dev/null 2> $f.scan.err
rc=$?
r=$(grep -c "released" $f.scan.err); w=$(grep -c "rules-consistency worker exited" $f.scan.err)
echo -e "$(basename $f)\t$rc\t$r\t$w"
rm -f $f.scan.err
