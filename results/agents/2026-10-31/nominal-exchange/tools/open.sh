#!/bin/bash
# open.sh BIN TAG : open seeds on three routes at 300 s, one at a time (one CPU)
N=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/nominal-exchange
cd $N
for f in r1600 r1646 r3403 r3602 r1536 r3777; do
  [ -f attr/$f.ofn ] || { cp ../r3-unannounced/seeds/$f.ofn attr/; cp ../r3-unannounced/gold/$f.json attr/$f.hermit.json; }
  for rt in nominals auto certified_nominals; do
    s=$(date +%s.%N)
    if [ $rt = auto ]; then out=$(timeout 300 ./$1 classify --lines attr/$f.ofn 2>/dev/null); else out=$(KM_ROUTE=$rt timeout 300 ./$1 classify --lines attr/$f.ofn 2>/dev/null); fi
    rc=$?; t=$(echo "$(date +%s.%N)-$s"|bc)
    printf "%s\t%s\t%s\t%.2f\t%s\n" $f $rt $rc $t "$(python3 -I verdict.py attr/$f.hermit.json <<< "$out")" >> runs/open-$2.tsv
  done
done
