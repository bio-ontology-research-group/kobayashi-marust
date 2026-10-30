#!/bin/bash
# ab3.sh FILE TAG -> file, rc/md5 for: final (memo on), final with KM_NO_FRONTEND_PASS_CACHE=1, km-i12 (no item 3), and memo hits
f=$1; tag=$2; b=$(basename $f .ofn); d=$S/ab-$tag; mkdir -p $d
run() { env -i PATH=$PATH HOME=$HOME TMPDIR=$HOME/tmp KM_TIMING=1 KM_THREADS=3 $2 timeout 60 $1 classify --lines $f > $d/$b.$3.out 2> $d/$b.$3.err; echo "$?:$(md5sum < $d/$b.$3.out | cut -c1-10)"; }
a=$(run $S/km-final "" on); c=$(run $S/km-final KM_NO_FRONTEND_PASS_CACHE=1 off); e=$(run $S/km-i12 "" i12)
h=$(grep -c "memo hits 1" $d/$b.on.err)
same=$([ "$a" = "$c" ] && [ "$a" = "$e" ] && echo same || echo DIFF)
echo -e "$b\t$a\t$c\t$e\t$h\t$same"
