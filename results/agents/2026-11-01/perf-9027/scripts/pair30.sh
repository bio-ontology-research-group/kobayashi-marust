#!/bin/bash
# pair30.sh LIST OUT.tsv: v1.5.3 and the fix on one CPU each, side by side, release flags, 240 s.
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/perf-9027
C=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/v150-corpus/files
V153=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/v153-release-assets-b5abf83a/km-v1.5.3-linux-x86_64
NEW=${NEW:-$S/km.pgo.fix2}
mkdir -p $S/pair
while read n; do
  $S/run.sh $V153 $C/$n.owl $S/pair/$n.v153 240 13 > $S/pair/$n.v153.sum &
  $S/run.sh $NEW $C/$n.owl $S/pair/$n.new 240 14 > $S/pair/$n.new.sum
  wait
  a=$(cat $S/pair/$n.v153.sum); b=$(cat $S/pair/$n.new.sum)
  # equality of the answer (sorted SUB/UNSAT lines and the header)
  if cmp -s <(sort $S/pair/$n.v153.out) <(sort $S/pair/$n.new.out); then same=same; else same=DIFF; fi
  echo -e "$n\t$(echo $a | grep -o 'rc=[0-9]*')\t$(echo $a | grep -o 'wall=[0-9.]*')\t$(echo $b | grep -o 'rc=[0-9]*')\t$(echo $b | grep -o 'wall=[0-9.]*')\t$same" >> $2
  rm -f $S/pair/$n.v153.out $S/pair/$n.new.out
done < $1
