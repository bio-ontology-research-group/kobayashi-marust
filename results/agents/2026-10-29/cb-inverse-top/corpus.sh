#!/bin/bash
# usage: corpus.sh LABEL  (uses $S/km.LABEL)
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/cb-inverse-top
C=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/v150-corpus/files
L=$1; mkdir -p $S/corpus/$L
for o in 3914 15803 4412 5475 15635 6682 850 1397 3156 13954; do
  out=$S/corpus/$L/$o.lines
  /usr/bin/time -f "%e %M" -o $S/corpus/$L/$o.time timeout 900 $S/km.$L classify --lines $C/ore_ont_$o.owl > $out 2> $S/corpus/$L/$o.err
  rc=$?
  grep -E "^(SUB|UNSAT)" $out | LC_ALL=C sort > $S/corpus/$L/$o.sorted
  echo "$o rc=$rc $(tail -1 $S/corpus/$L/$o.time) sub=$(grep -c ^SUB $S/corpus/$L/$o.sorted) unsat=$(grep -c ^UNSAT $S/corpus/$L/$o.sorted) $(head -1 $out)"
done
