#!/bin/bash
# Random validation: for seeds A..B, generate, run fast vs brute, and fast vs classifyQ
export TMPDIR=/mnt/data1/leechuck/km-work/v170/scratch/c1c/tmp
# (timeout 60 s, 8 GB) when the at-least sum is small. Output: rand-results.tsv.
S=/mnt/data1/leechuck/km-work/v170/scratch/c1c
P=${P:-/mnt/data1/leechuck/km-work/wt/v170-c1/lean/.lake/build/bin/km-sriq-fast-probe}
A=$1; B=$2; OUT=${3:-$S/rand-results.tsv}; REFT=${REFT:-60}
for seed in $(seq $A $B); do
  f=$S/${RDIR:-rand}/r$seed.sriq
  python3 $S/gen_random.py $seed $GENARGS > $f
  bnd=$(awk '$1=="ex"{s+=1} $1=="ge"{s+=$3} END{print s+0}' $f)
  b=$(KM_SRIQF_BRUTE=1 timeout ${BT:-300} $P --sriq $f 2>/dev/null | grep -E "BRUTE-|^decl" | head -1)
  r="skip"
  if [ "$bnd" -le "${REFMAX:-3}" ]; then
    r=$( (ulimit -v 8000000; KM_SRIQF_REF=1 timeout $REFT $P --sriq $f 2>/dev/null; echo "exit=$?") | grep -E "^AGREE|^DISAGREE|exit=" | tr '\n' ' ')
  fi
  printf "%s\t%s\t%s\t%s\n" "$seed" "$bnd" "$b" "$r" >> $OUT
done
