#!/bin/bash
p=$1; n=$(basename $p .ofn)
out=$(KM_THREADS=1 KM_ROUTE=ht_bridge KM_MERGE_TRACE=1 timeout 30 ./km.trace2 classify --lines $p 2>&1 >/dev/null)
sites=$(echo "$out" | grep -oE "(MERGE-STOP|INSTALL-FAIL) site=[0-9]+" | sort | uniq -c | awk '{printf "%s:%s:%s ", $2,$3,$1}')
last=$(echo "$out" | grep unsupported | tail -1 | cut -c1-90)
echo -e "$n\t$sites\t$last"
