#!/bin/bash
# usage: ofn_all.sh <km-binary> <outdir> <filelist>
km=$1; out=$2; mkdir -p $out
cat $3 | xargs -P 8 -I{} bash -c 'f="{}"; n=$(echo "$f" | md5sum | cut -c1-12); env -u KM_ROUTE timeout 120 '"$km"' ofn "$f" > '"$out"'/$n.json 2> '"$out"'/$n.err; echo $? > '"$out"'/$n.rc'
