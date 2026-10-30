#!/usr/bin/env bash
# Run the Rust tests that need real Lean checkers (the ones the CI recipe
# skips) against a directory of built checkers, without rebuilding Lean.
#
#   lean/run-checker-tests.sh CHECKER_DIR [extra cargo test filters...]
#
# CHECKER_DIR is a `lean/.lake/build/bin` from any build of the current Lean
# sources. The script exports every checker variable of the gates
# (lean/checker-env.sh) and runs the CI skip list one test at a time, then the
# three integration tests the CI skips, then the KM_LEAN_CHECKERS tests.
set -euo pipefail
repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
dir=${1:?usage: lean/run-checker-tests.sh CHECKER_DIR}
shift
# shellcheck source=lean/checker-env.sh
source "$repo_root/lean/checker-env.sh" "$dir"
export KM_TEST_LEAN_CHECKERS_DIR="$km_checker_dir"
cd "$repo_root/engine"
# Some checker-backed tests keep their evidence files in CARGO_TARGET_DIR.
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$repo_root/engine/target}"
# The CI skip list: the bare names inside `checker_tests=( ... )`.
skip_list=$(sed -n '/checker_tests=(/,/)/p' "$repo_root/.github/workflows/ci.yml" |
    grep -E '^ *[a-z0-9_]+ *$' | tr -d ' ')
# Lib tests that spawn workers find them the way the CI job sets them up.
worker_root=$(cd "$CARGO_TARGET_DIR/release" && pwd)
export KM_OFN_BIN="$worker_root/ofn" KM_ELC_BIN="$worker_root/elc"
export KM_ENGINE="$worker_root/kobayashi-marust" KM_TAB_BIN="$worker_root/tableau_cli"
for name in $skip_list "$@"; do
    cargo test --release --lib "$name" -- --test-threads=1 2>&1 |
        grep -E '^test |^test result' || true
done
for test in cb_live_state elc_certificate ht_taxonomy_certificate lean_checkers_dir; do
    cargo test --release --test "$test" -- --test-threads=1 2>&1 |
        grep -E '^test |^test result' || true
done
