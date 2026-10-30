#!/bin/bash
# run_tests2.sh TAG: rerun of the suites touched after tests-final (OOM retry checks only the step's own output)
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/rules-route-followups
cd /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/fix-rules-route-followups/engine
export CARGO_BUILD_JOBS=12 TMPDIR=$HOME/tmp
out=$S/tests-$1.log; : > $out
wait_headroom() { while true; do lim=$(awk '/CommitLimit/{print $2}' /proc/meminfo); cur=$(awk '/Committed_AS/{print $2}' /proc/meminfo); [ $(( (lim-cur)/1048576 )) -ge 30 ] && break; sleep 20; done; }
run() { echo "== $1" >> $out; shift; for try in 1 2 3 4; do wait_headroom; nice cargo test --release --features mimalloc "$@" > $out.step 2>&1; rc=$?; cat $out.step >> $out; if [ $rc != 0 ] && grep -q "out of memory" $out.step; then echo "retry after OOM" >> $out; continue; fi; break; done; echo "exit $rc" >> $out; }
run integration-mine --test rules_inert_sorts_routes --test data_assertions_carried --test empty_and_universal_data_ranges -- --test-threads=2
run lib-tableau-frontend --lib -- tableau:: frontend:: --test-threads=8
echo ALLDONE >> $out
