#!/bin/bash
# usage: measure_item2.sh <km> <outdir> <filelist>   (auto route, KM_TIMING on; records marker + time)
km=$1; out=$2; mkdir -p $out
cat $3 | xargs -P 6 -I{} bash -c 'f="{}"; n=$(echo "$f" | md5sum | cut -c1-12); s=$(date +%s.%N); env -u KM_ROUTE KM_TIMING=1 timeout 300 '"$km"' classify --lines "$f" > '"$out"'/$n.out 2> '"$out"'/$n.err; rc=$?; e=$(date +%s.%N); echo "$rc $(echo "$e - $s" | bc) $f" > '"$out"'/$n.rc'
