#!/bin/bash
# tests.sh: library and every integration target, one test thread, clean env.
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/sat578-opus
E=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/fix-sat578-opus/engine
cd $E; mkdir -p $S/tests
run() { env -i PATH=$PATH HOME=$HOME TMPDIR=$S/tmp KM_THREADS=1 CARGO_TARGET_DIR=$E/target timeout 7200 cargo test --release "$@" -- --test-threads=1; }
run --lib > $S/tests/lib.log 2>&1; echo "lib rc=$?" >> $S/tests/summary.txt
for f in tests/*.rs; do t=$(basename $f .rs); run --test $t > $S/tests/$t.log 2>&1; echo "$t rc=$?" >> $S/tests/summary.txt; done
echo DONE >> $S/tests/summary.txt
