#!/bin/bash
# run_tests.sh TAG: release test suites for the rules-route follow-ups
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/rules-route-followups
cd /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/fix-rules-route-followups/engine
export CARGO_BUILD_JOBS=12 TMPDIR=$HOME/tmp
out=$S/tests-$1.log; : > $out
wait_headroom() { while true; do lim=$(awk '/CommitLimit/{print $2}' /proc/meminfo); cur=$(awk '/Committed_AS/{print $2}' /proc/meminfo); [ $(( (lim-cur)/1048576 )) -ge 30 ] && break; sleep 20; done; }
T=""
for t in rules_inert_sorts_routes data_assertions_carried empty_and_universal_data_ranges universal_role_and_top_data_range cb_route_completeness forced_route_fail_closed top_nominal_data_successors rules_route finite_data_rule_normalization finite_rule_taxonomy ground_rule_source has_key_rules rule_independent_abox_clash transitive_rule_reduction constant_data_rule_normalization integer_data_rule_normalization unary_rule_normalization isolated_named_rule_normalization source_incremental_rules; do T="$T --test $t"; done
run() { echo "== $1" >> $out; shift; for try in 1 2 3; do wait_headroom; nice cargo test --release --features mimalloc "$@" >> $out 2>&1; rc=$?; grep -q "out of memory" $out && [ $rc != 0 ] && { echo "retry after OOM" >> $out; continue; }; break; done; echo "exit $rc" >> $out; }
run lib-targeted --lib -- orchestrate::inert_sorts frontend::rule_assertions frontend::pass_cache bigstack:: --test-threads=8
run integration $T --no-fail-fast -- --test-threads=4
run lib-orchestrate --lib -- orchestrate:: --test-threads=8
run lib-tableau-frontend --lib -- tableau:: frontend:: --test-threads=8
echo ALLDONE >> $out
