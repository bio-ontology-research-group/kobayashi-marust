#!/bin/bash
# nine.sh BIN LABEL : automatic route on the nine held-out inputs, sequential.
BIN=$1; LABEL=$2
D=$(dirname $0)/../data/nine-$LABEL; mkdir -p $D
for n in ${NINE:-4796 6132 9899 3917 11378 12191 9151 9577 12128}; do
  TO=240 $(dirname $0)/run.sh $BIN $n $D/$n > /dev/null
  python3 $(dirname $0)/diff_ref.py $n $D/$n.out $D/canon >> $D/refs.jsonl
done
cat $D/*.time > $D/summary.txt
