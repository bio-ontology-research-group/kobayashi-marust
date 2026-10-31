#!/bin/bash
# usage: time.sh <km-binary> [reps]   times hub_test.ofn per route, prints median
D=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/data-values-3
export TMPDIR=$D/tmp; mkdir -p $TMPDIR
bin=$1; reps=${2:-3}
for route in auto nominals certified_nominals nominal_ni_abox certified_card_proxy_abox; do
  ts=()
  for i in $(seq $reps); do
    s=$(date +%s.%N)
    if [ $route = auto ]; then env -u KM_ROUTE timeout 60 $bin classify --lines $D/hub_test.ofn > $D/out.$route.txt 2>/dev/null; rc=$?
    else KM_ROUTE=$route timeout 60 $bin classify --lines $D/hub_test.ofn > $D/out.$route.txt 2>/dev/null; rc=$?; fi
    e=$(date +%s.%N); ts+=($(echo "$e - $s" | bc))
  done
  med=$(printf "%s\n" "${ts[@]}" | sort -n | awk '{a[NR]=$1} END{print a[int((NR+1)/2)]}')
  echo "$(basename $bin) $route rc=$rc median=$med all=${ts[*]} lines=$(wc -l < $D/out.$route.txt) md5=$(sort $D/out.$route.txt | md5sum | cut -c1-8)"
done
