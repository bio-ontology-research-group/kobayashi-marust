#!/bin/bash
# ore_cls.sh BIN_TAG FILE : km classify --lines on the automatic route, KM_THREADS=1, 240 s, one CPU; prints stem, tag, rc, seconds, answer digest, line counts
S=$S
b=$1; f=$2; stem=$(basename $f); stem=${stem%.*}
mkdir -p $S/ore-out
t0=$(date +%s.%N)
env -i PATH=$PATH HOME=$HOME KM_THREADS=1 timeout 240 $S/tools/pin-$b classify --lines $f > $S/ore-out/$stem.$b.raw 2> $S/ore-out/$stem.$b.err
rc=$?
t=$(echo "$(date +%s.%N)-$t0" | bc)
grep -E '^(SUB|UNSAT|CONSISTENT|DROPPED)' $S/ore-out/$stem.$b.raw | sort > $S/ore-out/$stem.$b.ans
rm -f $S/ore-out/$stem.$b.raw
d=$(sha256sum < $S/ore-out/$stem.$b.ans | cut -c1-16)
printf "%s\t%s\t%s\t%.2f\t%s\t%s\t%s\n" $stem $b $rc $t $d $(grep -c '^SUB' $S/ore-out/$stem.$b.ans) $(grep -c '^UNSAT' $S/ore-out/$stem.$b.ans)
