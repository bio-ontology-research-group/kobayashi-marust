#!/bin/bash
# onoff2.sh KM FILE TAG -> file, released, workers_on, rc_on, rc_off, same, t_on, t_off
# Like review-inert-sorts/onoff.sh, plus worker stderr/rc capture (captab.sh, cap-TAG/).
km=$1; f=$2; tag=$3; b=$(basename $f .ofn); d=$S/oo-$tag; mkdir -p $d $S/cap-$tag
run() { env -i PATH=$PATH HOME=$HOME TMPDIR=$HOME/tmp KM_TIMING=1 CAP_DIR=$S/cap-$tag KM_TAB_BIN=$S/captab.sh KM_REAL_TAB=$km CAP_TAG=$b-$2 $1 timeout 60 $km classify --lines $f > $d/$b.$2.out 2> $d/$b.$2.err; echo $?; }
s=$(date +%s.%N); rc1=$(run "" on); t1=$(echo "$(date +%s.%N) - $s" | bc)
s=$(date +%s.%N); rc2=$(run "KM_RULES_KEEP_INERT_SORTS=1" off); t2=$(echo "$(date +%s.%N) - $s" | bc)
rel=$(grep -o "released [0-9]* inert" $d/$b.on.err | head -1 | awk '{print $2}'); w=$(grep -c "rules-consistency worker exited" $d/$b.on.err)
same=$(cmp -s $d/$b.on.out $d/$b.off.out && echo same || echo DIFF)
echo -e "$b\t${rel:-0}\t$w\t$rc1\t$rc2\t$same\t$t1\t$t2"
