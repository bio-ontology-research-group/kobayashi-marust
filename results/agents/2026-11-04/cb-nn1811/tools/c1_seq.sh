#!/bin/bash
# c1_seq.sh BASE_BIN NEW_BIN : the 300-input sample of the C1 regression pool
# (c1-sample-300.txt: ORE numbers drawn with random.Random(1811) from the admitted rows of
# .work/v152-correctness-1920/full-candidate-inputs-ws.json), one process at a time, base then new
# on each input (one.sh, release flags, 60 s cap), compared with the pinned references.
T=$(dirname $(readlink -f $0)); B=$1; N=$2
while read -r n; do
  CAP=60 $T/one.sh $B $n base; CAP=60 $T/one.sh $N $n new
done < $T/c1-sample-300.txt
