#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
lean_root="$repo_root/lean"
engine_root="$repo_root/engine"
bin_root="$lean_root/.lake/build/bin"
target_root="$repo_root/.work/target"

preflight="$repo_root/tools/workspace-preflight.sh"
if [[ -x "$preflight" ]]; then
    "$preflight"
else
    free_kib=$(df -Pk "$repo_root" | awk 'NR == 2 { print $4 }')
    available_kib=$(awk '/^MemAvailable:/ { print $2 }' /proc/meminfo)
    (( free_kib >= 20 * 1024 * 1024 )) || {
        echo "HT certification gate requires at least 20 GiB free disk" >&2
        exit 1
    }
    (( available_kib >= 16 * 1024 * 1024 )) || {
        echo "HT certification gate requires at least 16 GiB available memory" >&2
        exit 1
    }
fi

checkers=(
    ht-regular-cert-check
    ht-cover-obstruction-check
    ht-endpoint-role-evidence-check
    ht-cover-refinement-check
    ht-projection-cert-check
    ht-frontier-check
    ht-production-blocking-check
    ht-equality-production-blocking-check
    ht-equality-production-trace-check
    ht-cardinality-frontier-check
    ht-native-abox-taxonomy-matrix-cert-check
    ht-native-abox-cardinality-taxonomy-cert-check
    ht-native-abox-taxonomy-source-cert-check
    ht-native-abox-cardinality-taxonomy-source-cert-check
    ht-joint-native-abox-classification-cert-check
)

(
    cd "$lean_root"
    LEAN_NUM_THREADS=4 lake build
    LEAN_NUM_THREADS=4 lake build ContextCalculus.HypertableauCertificationSurface
    # The default Lake facets build the libraries, not every native checker.
    # Build the exact executables consumed below so an old binary can never
    # make a cross-language certification test pass or fail spuriously.
    LEAN_NUM_THREADS=4 lake build "${checkers[@]}"
)

for checker in "${checkers[@]}"; do
    [[ -x "$bin_root/$checker" ]] || {
        echo "missing Lean checker: $bin_root/$checker" >&2
        exit 1
    }
done

(
    cd "$engine_root"
    export CARGO_TARGET_DIR="$target_root"
    export KM_HT_TEST_REGULAR_LEAN_CHECKER="$bin_root/ht-regular-cert-check"
    export KM_HT_TEST_LEAN_PROJECTION_CHECKER="$bin_root/ht-projection-cert-check"
    export KM_HT_LEAN_FRONTIER_CHECKER="$bin_root/ht-frontier-check"
    export KM_HT_LEAN_CARDINALITY_FRONTIER_CHECKER="$bin_root/ht-cardinality-frontier-check"
    export KM_HT_TEST_LEAN_FRONTIER_CHECKER="$bin_root/ht-frontier-check"
    export KM_HT_LEAN_PRODUCTION_BLOCKING_CHECKER="$bin_root/ht-production-blocking-check"
    export KM_HT_TEST_LEAN_PRODUCTION_BLOCKING_CHECKER="$bin_root/ht-production-blocking-check"
    export KM_HT_LEAN_EQUALITY_PRODUCTION_BLOCKING_CHECKER="$bin_root/ht-equality-production-blocking-check"
    export KM_HT_TEST_LEAN_EQUALITY_PRODUCTION_BLOCKING_CHECKER="$bin_root/ht-equality-production-blocking-check"
    export KM_HT_LEAN_EQUALITY_PRODUCTION_TRACE_CHECKER="$bin_root/ht-equality-production-trace-check"
    export KM_HT_TEST_LEAN_EQUALITY_PRODUCTION_TRACE_CHECKER="$bin_root/ht-equality-production-trace-check"
    export KM_HT_TEST_LEAN_CARDINALITY_FRONTIER_CHECKER="$bin_root/ht-cardinality-frontier-check"
    export KM_HT_TEST_LEAN_NATIVE_ABOX_TAXONOMY_MATRIX_CHECKER="$bin_root/ht-native-abox-taxonomy-matrix-cert-check"
    export KM_HT_TEST_LEAN_NATIVE_ABOX_CARDINALITY_TAXONOMY_MATRIX_CHECKER="$bin_root/ht-native-abox-cardinality-taxonomy-cert-check"
    export KM_HT_TEST_LEAN_NATIVE_ABOX_TAXONOMY_SOURCE_CHECKER="$bin_root/ht-native-abox-taxonomy-source-cert-check"
    export KM_HT_TEST_LEAN_NATIVE_ABOX_CARDINALITY_TAXONOMY_SOURCE_CHECKER="$bin_root/ht-native-abox-cardinality-taxonomy-source-cert-check"
    export KM_HT_TEST_LEAN_JOINT_NATIVE_ABOX_CLASSIFICATION_CHECKER="$bin_root/ht-joint-native-abox-classification-cert-check"

    cargo test --release equality_decision_pairwise_blocks_and_checks_a_satisfiable_cycle -- --nocapture
    cargo test --release equality_production_blocking_checks_rejection_provenance -- --nocapture
    cargo test --release native_abox_production_blocking_checks_joint_rejection_provenance -- --nocapture
    cargo test --release equality_and_cardinality_folds_copy_incoming_blocker_edges -- --nocapture
    cargo test --release source_matrix_passes_real_lean_checker -- --nocapture
    cargo test --release certified_input_coverage_matches_the_lean_truth_table -- --nocapture
    cargo test --release regular_certificate_serializes_general_guarded_residual_bodies -- --nocapture
    cargo test --release --test ht_taxonomy_certificate -- --nocapture
)
