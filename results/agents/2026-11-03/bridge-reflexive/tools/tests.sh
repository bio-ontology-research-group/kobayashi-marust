#!/bin/bash
# tests.sh OUTDIR : the library suite and every integration target, one by
# one, clean environment (no release flags), KM_THREADS=1, --test-threads=1.
OUT=$1; mkdir -p $OUT
W=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/fix-bridge-reflexive/engine
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/bridge-reflexive
E="env -i PATH=$PATH HOME=$HOME KM_THREADS=1 TMPDIR=$S/tmp CARGO_TARGET_DIR=$W/target"
cd $W
$E nice cargo test --release --lib -- --test-threads=1 > $OUT/lib.log 2>&1
grep -E '^test result' $OUT/lib.log > $OUT/summary.txt
grep -E '^test .* FAILED$' $OUT/lib.log | sed 's/^test //; s/ \.\.\. FAILED$//' | sort > $OUT/lib-failures.txt
for t in tests/*.rs; do n=$(basename $t .rs)
  $E nice cargo test --release --test $n -- --test-threads=1 > $OUT/it-$n.log 2>&1
  echo "$n rc=$? $(grep -E '^test result' $OUT/it-$n.log | tail -1)" >> $OUT/summary.txt
done
echo DONE >> $OUT/summary.txt
