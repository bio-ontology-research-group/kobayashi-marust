#!/bin/bash
# pairrc.sh LIST OUT.tsv: the fix on CPU 13 and the v1.5.5 preview RC on CPU 14, side by side.
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/perf-9027
C=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/v150-corpus/files
RC=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/pgo-v155-preview/km-v1.5.5-rc-pgo
mkdir -p $S/pairrc
while read n; do
  $S/run.sh $RC $C/$n.owl $S/pairrc/$n.rc 240 14 > $S/pairrc/$n.rc.sum &
  $S/run.sh $S/km.pgo.fix2 $C/$n.owl $S/pairrc/$n.new 240 13 > $S/pairrc/$n.new.sum
  wait
  if cmp -s <(sort $S/pairrc/$n.rc.out) <(sort $S/pairrc/$n.new.out); then same=same; else same=DIFF; fi
  echo -e "$n\t$(grep -o 'rc=[0-9]*' $S/pairrc/$n.rc.sum)\t$(grep -o 'wall=[0-9.]*' $S/pairrc/$n.rc.sum)\t$(grep -o 'rc=[0-9]*' $S/pairrc/$n.new.sum)\t$(grep -o 'wall=[0-9.]*' $S/pairrc/$n.new.sum)\t$same" >> $2
  rm -f $S/pairrc/$n.rc.out $S/pairrc/$n.new.out
done < $1
