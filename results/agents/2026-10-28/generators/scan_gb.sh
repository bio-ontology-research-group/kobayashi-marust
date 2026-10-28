#!/bin/bash
# scan each file in nominal mode, keep only a per-file summary of ground-body clauses
S=$1; km=$2; list=$3; out=$4; mkdir -p $out
cat $list | xargs -P 10 -I{} bash -c 'f="{}"; n=$(basename "$f" .owl); KM_ROUTE=nominals timeout 120 '"$km"' ofn "$f" > '"$out"'/$n.json 2>/dev/null; python3 '"$S"'/tools/ground_body.py '"$out"'/$n.json | grep -v "^empty-head:\|^head:" | sed "s/^/$n /" > '"$out"'/$n.sum; rm -f '"$out"'/$n.json'
