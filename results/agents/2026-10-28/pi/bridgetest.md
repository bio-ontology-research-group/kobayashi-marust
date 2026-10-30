# Task: update one stale unit test in the KM reasoner (Rust)

Your current directory is the git worktree .work/worktrees/fix-bridge-literal-test (branch fix/v154-bridge-literal-test, from development/v1.5.4). Work and commit only here. Never push, never run `ssh ws`, kill processes only by PID. Build from engine/ with `CARGO_TARGET_DIR=$PWD/target nice cargo ...` (this sets a target directory of your own). Keep scratch files in /tmp/claude-1000/-home-leechuck--herdr-worktrees-kobayashi-marust-worktree-paper/0285edda-d83d-4be5-8ecb-bb0aeb5575cb/scratchpad/pi/bridgetest/.

The unit test `konclude_ht::bridge::tests::bridge_tbox_datatype_extension_literal_is_head_only` in engine/src/konclude_ht/bridge.rs fails. Its second assertion expects the bridge to decline `EquivalentClasses(C DataSomeValuesFrom(p rdfs:Literal))`. The frontend now rewrites that restriction to the unqualified `DataMinCardinality(1 p)`, so the bridge correctly admits the input. A reviewed patch that turns the assertion into a positive check is at /tmp/claude-1000/-home-leechuck--herdr-worktrees-kobayashi-marust-worktree-paper/0285edda-d83d-4be5-8ecb-bb0aeb5575cb/scratchpad/pi/bridgetest/bridge-test.patch.

1. Apply the patch with `git apply`. If it does not apply cleanly, make the same change by hand.
2. Read the changed test. Check that its claim holds: A ⊑ ∃p.integer ⊑ ∃p.Literal ≡ C gives A ⊑ C, and C ⊑ A does not hold.
3. Run `cargo test --release --lib bridge_tbox_datatype_extension`, then `cargo test --release --lib konclude_ht::`. Report the exact `test result` lines.
4. Commit only this change. End the commit message with:
   Co-Authored-By: kimi-k2.7-code via pi-opencode <noreply@opencode.ai>
5. Report the commit hash and the test results. Mark what you verified by running it.
