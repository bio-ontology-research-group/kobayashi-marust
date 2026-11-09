#!/bin/bash
# heldout_pair.sh BASE NEW LABEL : the 16 held-out inputs of
# docs/V1.5.5-STATUS.md, each run on BASE and NEW at the same time (two KM
# processes, the same host load for both), release flags, 240 s (one.sh).
# Rows go to .work/agent-scratch/bridge-satcache/runs/summary.tsv with the
# labels LABEL-base and LABEL-new.
T=$(dirname $(readlink -f $0)); BASE=$1; NEW=$2; L=$3
for n in 4903 11647 4796 3917 11378 12191 9151 9577 6132 9899 16315 10838 3087 7557 10926 12128; do
  $T/one.sh $BASE $n $L-base & $T/one.sh $NEW $n $L-new & wait
done
