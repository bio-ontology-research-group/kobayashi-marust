#!/usr/bin/env bash
# Targeted test runs for the certificate-defect fixes (release, real checkers).
W=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work
R=$W/worktrees/fix-certificate-defects
B=$R/lean/.lake/build/bin
S=$W/agent-scratch/certificate-defects/tests
mkdir -p $S
cd $R/engine
export LEAN_STACK_SIZE_KB=262144
run() { name=$1; shift; echo "== $name"; "$@" > $S/$name.log 2>&1; echo "exit $?"; grep "^test result" $S/$name.log; }
run elc-lib env KM_ELC_TEST_LEAN_CHECKER=$B/elc-cert-check cargo test --release --lib elcomplete:: -- --test-threads=1
run lean-checkers-lib cargo test --release --lib lean_checkers -- --test-threads=1
run lean-checkers-dir-stub cargo test --release --test lean_checkers_dir -- --test-threads=1
run lean-checkers-dir-real env KM_TEST_LEAN_CHECKERS_DIR=$B cargo test --release --test lean_checkers_dir -- --test-threads=1
run elc-certificate env KM_ELC_TEST_LEAN_CHECKER=$B/elc-cert-check KM_ELC_LEAN_CERT_CHECKER=$B/elc-cert-check cargo test --release --test elc_certificate -- --test-threads=1
run cb-live-state cargo test --release --test cb_live_state -- --test-threads=1
run lib-all-noenv cargo test --release --lib -- --test-threads=4
echo all-done
