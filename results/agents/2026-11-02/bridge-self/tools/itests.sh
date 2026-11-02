#!/bin/bash
# itests.sh OUTDIR : library tests and every integration target, one by one,
# KM_THREADS=1, --test-threads=1, release.
OUT=$1; mkdir -p $OUT
W=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/fix-bridge-self/engine
export CARGO_TARGET_DIR=$W/target KM_THREADS=1
export TMPDIR=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/bridge-self/tmp
cd $W
nice cargo test --release --lib -- --test-threads=1 > $OUT/lib.log 2>&1
grep -E '^test result' $OUT/lib.log > $OUT/summary.txt
grep -E '^test .* FAILED$' $OUT/lib.log | sed 's/^test //; s/ \.\.\. FAILED$//' | sort > $OUT/lib-failures.txt
for t in tests/*.rs; do n=$(basename $t .rs)
  nice cargo test --release --test $n -- --test-threads=1 > $OUT/it-$n.log 2>&1
  echo "$n rc=$? $(grep -E '^test result' $OUT/it-$n.log | tail -1)" >> $OUT/summary.txt
done
