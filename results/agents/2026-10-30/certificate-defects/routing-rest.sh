#!/usr/bin/env bash
# Steps of run-routing-certification-gate.sh after source_module_reuse (lines 417-445), run with set -e off so every step reports.
engine_root=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/fix-certificate-defects/engine; target_root=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/certificate-defects/gate/target; export LEAN_STACK_SIZE_KB=262144 CARGO_BUILD_JOBS=8
cd "$engine_root"
CARGO_TARGET_DIR="$target_root" cargo test --release --lib \
    incremental_activation::tests::
CARGO_TARGET_DIR="$target_root" cargo test --release --lib \
    frontend::separable_abox_elision_tests::
CARGO_TARGET_DIR="$target_root" cargo test --release --lib \
    orchestrate::abox_quotient::tests::
CARGO_TARGET_DIR="$target_root" cargo test --release --test incremental_reasoning
CARGO_TARGET_DIR="$target_root" cargo test --release --test incremental_cb_reasoning
CARGO_TARGET_DIR="$target_root" cargo test --release --test incremental_ht_reasoning
CARGO_TARGET_DIR="$target_root" cargo test --release --test source_incremental_nominals
CARGO_TARGET_DIR="$target_root" cargo test --release --test source_incremental_rules
CARGO_TARGET_DIR="$target_root" cargo test --release --test finite_rule_taxonomy
CARGO_TARGET_DIR="$target_root" cargo test --release --test finite_data_rule_normalization
CARGO_TARGET_DIR="$target_root" cargo test --release --test constant_data_rule_normalization
CARGO_TARGET_DIR="$target_root" cargo test --release --test inverse_role_chains
CARGO_TARGET_DIR="$target_root" cargo test --release --lib endpoint_transitivity_tests
CARGO_TARGET_DIR="$target_root" cargo test --release --test endpoint_transitivity
CARGO_TARGET_DIR="$target_root" cargo test --release --test ground_rule_source
CARGO_TARGET_DIR="$target_root" cargo test --release --test rule_independent_abox_clash
CARGO_TARGET_DIR="$target_root" cargo test --release --test symbolic_source_classification
CARGO_TARGET_DIR="$target_root" cargo test --release --lib initialized_queue_less_node_does_not_starve_other_completion_work
CARGO_TARGET_DIR="$target_root" cargo test --release --lib orchestrate::symbolic_source::tests
CARGO_TARGET_DIR="$target_root" cargo test --release --lib full_symbolic_source_bounds_execute_with_float_data
CARGO_TARGET_DIR="$target_root" cargo test --release --lib finite_rule_model_tests
CARGO_TARGET_DIR="$target_root" cargo test --release --lib empty_grounding_model_tests
CARGO_TARGET_DIR="$target_root" cargo test --release --test explain_cli
CARGO_TARGET_DIR="$target_root" cargo test --release --lib orchestrate::tests::graph_json
CARGO_TARGET_DIR="$target_root" cargo test --release --lib orchestrate::tests::reachability_graph_json
CARGO_TARGET_DIR="$target_root" cargo test --release --test graph_json_cli
