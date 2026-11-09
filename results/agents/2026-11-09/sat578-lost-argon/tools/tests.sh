#!/bin/bash
# tests.sh: library and every integration target, one test thread, clean env.
set -u
W=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/fix-sat578-lost-argon
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/sat578-lost-argon
E=$W/engine
D=$W/results/agents/2026-11-09/sat578-lost-argon/data/tests
mkdir -p "$S/tmp" "$S/tests" "$D"
cd "$E" || exit 1

run_cargo() {
  env -i PATH="$PATH" HOME="$HOME" TMPDIR="$S/tmp" KM_THREADS=1 CARGO_TARGET_DIR="$E/target" timeout 7200 cargo test --release "$@"
}

# Pre-build all test targets once so per-target runs do not re-invoke rustc
run_cargo --lib --no-run > "$S/tests/build-lib.log" 2>&1
run_cargo --tests --no-run > "$S/tests/build-tests.log" 2>&1

: > "$D/summary.txt"
run_cargo --lib -- --test-threads=1 > "$S/tests/lib.log" 2>&1
echo "lib rc=$?" >> "$D/summary.txt"
grep '^test .* \.\.\. ' "$S/tests/lib.log" | LC_ALL=C sort > "$D/lib-results.txt"
grep '^    [a-z]' "$S/tests/lib.log" | LC_ALL=C sort > "$D/lib-failures.txt"

for f in tests/*.rs; do
  t=$(basename "$f" .rs)
  run_cargo --test "$t" -- --test-threads=1 > "$S/tests/$t.log" 2>&1
  rc=$?
  if [ "$rc" -ne 0 ]; then
    # Rerun once alone in case of transient host load (common.md)
    run_cargo --test "$t" -- --test-threads=1 > "$S/tests/$t.log" 2>&1
    rc=$?
  fi
  echo "$t rc=$rc" >> "$D/summary.txt"
done
echo DONE >> "$D/summary.txt"
