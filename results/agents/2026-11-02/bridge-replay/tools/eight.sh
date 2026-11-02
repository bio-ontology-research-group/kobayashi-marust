#!/bin/bash
# eight.sh BIN LABEL [PAR] : automatic route on the eight held-out inputs,
# at most two at a time, each followed by the reference comparison.
BIN=$1; LABEL=$2; PAR=${3:-2}
T=$(dirname $(readlink -f $0))
D=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/bridge-replay/data/eight-$LABEL; mkdir -p $D
one() { n=$1; $T/run.sh $BIN $n $D/$n > /dev/null; python3 -I $T/diff_ref.py $n $D/$n.out $D/canon > $D/$n.ref.json; }
export -f one; export T D BIN
printf '%s\n' ${EIGHT:-3917 11378 12191 9151 9577 6132 9899 12128} | xargs -P $PAR -I{} bash -c 'one {}'
cat $D/*.time > $D/summary.txt; cat $D/*.ref.json > $D/refs.jsonl
