#!/bin/bash
# pmp-child.sh BIN ONT OUT NSAMPLES INTERVAL DELAY [args]: run and sample the 'tableau' worker child (or main)
BIN=$1; ONT=$2; OUT=$3; N=$4; I=$5; D=$6; shift 6
D0=$(dirname $0)
TO=${TO:-240} $D0/run.sh $BIN $ONT $OUT "$@" > /dev/null 2>&1 &
sleep $D
rm -f $OUT.pmp
for i in $(seq $N); do
  P=$(pgrep -f "$(basename $BIN) tableau" | head -1)
  [ -z "$P" ] && P=$(pgrep -f "$(basename $BIN) classify" | tail -1)
  [ -z "$P" ] && break
  gdb -p $P -batch -ex "thread apply all bt 50" 2>/dev/null | grep '^#' >> $OUT.pmp
  echo "----" >> $OUT.pmp
  sleep $I
done
wait
