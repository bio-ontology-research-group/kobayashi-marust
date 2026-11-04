#!/bin/bash
# heldout_pair.sh BASE_BIN NEW_BIN : the 16 held-out inputs of docs/V1.5.5-STATUS.md,
# base and new on the same input side by side (one.sh, release flags, 240 s);
# 12128 and 10926 (18 GiB) run alone, base then new.
T=$(dirname $(readlink -f $0)); B=$1; N=$2
for n in 4903 11647 4796 3917 11378 12191 9151 9577 6132 9899 16315 10838 3087 7557; do
  $T/one.sh $B $n base & $T/one.sh $N $n new & wait
done
for n in 12128 10926; do $T/one.sh $B $n base; $T/one.sh $N $n new; done
