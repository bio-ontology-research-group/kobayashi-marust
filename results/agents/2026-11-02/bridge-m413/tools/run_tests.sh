#!/bin/bash
# run_tests.sh OUTDIR : library tests and every integration target, one test
# thread, KM_THREADS=1, release profile (this worktree's engine/target).
O=$1; mkdir -p $O
W=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/fix-bridge-m413/engine
cd $W
export KM_THREADS=1 TMPDIR=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/bridge-m413/tmp
CARGO_TARGET_DIR=$W/target nice cargo test --release --lib -- --test-threads=1 > $O/test-lib.log 2>&1
echo "lib rc=$?" > $O/test-summary.txt
for t in tests/*.rs; do n=$(basename $t .rs)
  echo "=== $n" >> $O/test-int.log
  CARGO_TARGET_DIR=$W/target nice cargo test --release --test $n -- --test-threads=1 >> $O/test-int.log 2>&1
  echo "rc=$? $n" >> $O/test-int.log
done
echo DONE >> $O/test-summary.txt
