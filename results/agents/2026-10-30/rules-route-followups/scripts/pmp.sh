#!/bin/bash
# pmp.sh BIN INPUT N: sample main-thread stacks of a classify run
cd "$(dirname "$0")"
KM_TIMING=1 TMPDIR=$HOME/tmp $1 classify $2 > /dev/null 2> pmp.err &
P=$!
for i in $(seq 1 $3); do
  /bin/sleep 0.6
  echo "[$i passes=$(grep -c 'in-process frontend' pmp.err)] $(gdb -p $P -batch -ex 'thread 1' -ex 'bt 30' 2>/dev/null | grep '^#' | sed -E 's/^#[0-9]+ +(0x[0-9a-f]+ in )?//; s/ \(.*//' | head -18 | tr '\n' '<')"
done
wait $P
