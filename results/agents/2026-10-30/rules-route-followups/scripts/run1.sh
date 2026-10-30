#!/bin/bash
# run1.sh KM FILE TAG -> one classify with captured worker stderr
km=$1; f=$2; tag=$3; b=$(basename $f .ofn); o=$S/out-$tag; mkdir -p $o
env -i PATH=$PATH HOME=$HOME KM_TIMING=1 KM_TAB_BIN=$S/captab.sh KM_REAL_TAB=$km CAP_TAG=$tag-$b ${EXTRA} timeout 60 $km classify --lines $f > $o/$b.out 2> $o/$b.err
echo -e "$b\t$?"
