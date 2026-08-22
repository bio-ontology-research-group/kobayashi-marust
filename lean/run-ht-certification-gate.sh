#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
lean_root="$repo_root/lean"
engine_root="$repo_root/engine"
bin_root="$lean_root/.lake/build/bin"
target_root="$repo_root/.work/target"
artifact_root="$repo_root/.work/artifacts"
surface_log="$artifact_root/ht-certification-surface.log"

mkdir -p "$artifact_root"

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
    ht-cert-check
    ht-eq-cert-check
    ht-cardinality-cert-check
    ht-regular-cert-check
    ht-regular-cardinality-cert-check
    ht-regular-decision-cert-check
    ht-cover-obstruction-check
    ht-endpoint-role-evidence-check
    ht-cover-refinement-check
    ht-projection-cert-check
    ht-frontier-check
    ht-address-refinement-check
    ht-doubling-trace-check
    ht-cardinality-doubling-trace-check
    ht-rooted-cardinality-doubling-trace-check
    ht-ordinary-production-run-check
    ht-cardinality-production-run-check
    ht-rooted-cardinality-production-run-check
    ht-production-blocking-check
    ht-production-trace-check
    ht-finite-production-terminal-check
    ht-regular-production-terminal-check
    ht-equality-production-blocking-check
    ht-equality-production-trace-check
    ht-equality-production-terminal-check
    ht-cardinality-frontier-check
    ht-rooted-cardinality-frontier-check
    ht-native-abox-decision-cert-check
    ht-native-abox-source-decision-cert-check
    ht-native-abox-taxonomy-cert-check
    ht-native-abox-taxonomy-matrix-cert-check
    ht-native-abox-cardinality-taxonomy-cert-check
    ht-direct-native-abox-cardinality-taxonomy-cert-check
    ht-mixed-native-abox-cardinality-taxonomy-cert-check
    ht-native-abox-taxonomy-source-cert-check
    ht-native-abox-cardinality-taxonomy-source-cert-check
    ht-joint-native-abox-classification-cert-check
    ht-anchored-premises-check
    ht-anchored-eq-cert-check
    ht-anchored-cardinality-cert-check
    ht-taxonomy-cert-check
)

# Keep the release gate exhaustive as checker executables are added. A new HT
# checker in the Lake manifest must be deliberately added above and exercised
# by this gate rather than silently remaining outside release validation.
mapfile -t declared_ht_checkers < <(
    awk '
        /^name = "ht-/ {
            value = $3
            gsub(/"/, "", value)
            print value
        }
    ' "$lean_root/lakefile.toml" | sort -u
)
checker_drift=$(
    comm -3 \
        <(printf '%s\n' "${checkers[@]}" | sort -u) \
        <(printf '%s\n' "${declared_ht_checkers[@]}")
)
if [[ -n "$checker_drift" ]]; then
    echo "HT checker manifest and certification gate differ:" >&2
    echo "$checker_drift" >&2
    exit 1
fi

(
    cd "$lean_root"
    LEAN_NUM_THREADS=4 lake build
    # The default Lake facets build the libraries, not every native checker.
    # Build the exact executables consumed below so an old binary can never
    # make a cross-language certification test pass or fail spuriously.
    LEAN_NUM_THREADS=4 lake build "${checkers[@]}"
)

# Build the release theorem surface separately and retain its axiom report.
# A cached replay still emits the `#print axioms` messages, so this audit does
# not silently disappear on incremental builds.
(
    cd "$lean_root"
    LEAN_NUM_THREADS=4 lake build ContextCalculus.HypertableauCertificationSurface \
        2>&1 | tee "$surface_log"
)

if grep -q 'sorryAx' "$surface_log"; then
    echo "HT certification surface depends on an admitted theorem" >&2
    exit 1
fi

surface_theorems=(
    certifiedHTGlobalPublication
    certifiedHTRegularTaxonomyPublication
    certifiedHTCardinalityTaxonomyPublication
    certifiedHTNativeABoxTaxonomyPublication
    certifiedHTNativeABoxCardinalityTaxonomyPublication
)
for theorem in "${surface_theorems[@]}"; do
    grep -q "HypertableauCertificationSurface.*$theorem\|'ContextCalculus.Hypertableau.$theorem'" \
        "$surface_log" || {
        echo "missing HT certification-surface axiom audit: $theorem" >&2
        exit 1
    }
done

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
    export KM_HT_LEAN_FRONTIER_CHECKER="$bin_root/ht-address-refinement-check"
    export KM_HT_LEAN_CARDINALITY_FRONTIER_CHECKER="$bin_root/ht-cardinality-frontier-check"
    export KM_HT_LEAN_ROOTED_CARDINALITY_FRONTIER_CHECKER="$bin_root/ht-rooted-cardinality-frontier-check"
    export KM_HT_TEST_LEAN_FRONTIER_CHECKER="$bin_root/ht-address-refinement-check"
    export KM_HT_LEAN_DOUBLING_TRACE_CHECKER="$bin_root/ht-doubling-trace-check"
    export KM_HT_TEST_LEAN_DOUBLING_TRACE_CHECKER="$bin_root/ht-doubling-trace-check"
    export KM_HT_LEAN_CARDINALITY_DOUBLING_TRACE_CHECKER="$bin_root/ht-cardinality-doubling-trace-check"
    export KM_HT_TEST_LEAN_CARDINALITY_DOUBLING_TRACE_CHECKER="$bin_root/ht-cardinality-doubling-trace-check"
    export KM_HT_LEAN_ROOTED_CARDINALITY_DOUBLING_TRACE_CHECKER="$bin_root/ht-rooted-cardinality-doubling-trace-check"
    export KM_HT_TEST_LEAN_ROOTED_CARDINALITY_DOUBLING_TRACE_CHECKER="$bin_root/ht-rooted-cardinality-doubling-trace-check"
    export KM_HT_LEAN_ORDINARY_PRODUCTION_RUN_CHECKER="$bin_root/ht-ordinary-production-run-check"
    export KM_HT_TEST_LEAN_ORDINARY_PRODUCTION_RUN_CHECKER="$bin_root/ht-ordinary-production-run-check"
    export KM_HT_LEAN_CARDINALITY_PRODUCTION_RUN_CHECKER="$bin_root/ht-cardinality-production-run-check"
    export KM_HT_TEST_LEAN_CARDINALITY_PRODUCTION_RUN_CHECKER="$bin_root/ht-cardinality-production-run-check"
    export KM_HT_LEAN_ROOTED_CARDINALITY_PRODUCTION_RUN_CHECKER="$bin_root/ht-rooted-cardinality-production-run-check"
    export KM_HT_TEST_LEAN_ROOTED_CARDINALITY_PRODUCTION_RUN_CHECKER="$bin_root/ht-rooted-cardinality-production-run-check"
    export KM_HT_LEAN_PRODUCTION_BLOCKING_CHECKER="$bin_root/ht-production-blocking-check"
    export KM_HT_TEST_LEAN_PRODUCTION_BLOCKING_CHECKER="$bin_root/ht-production-blocking-check"
    export KM_HT_LEAN_PRODUCTION_TRACE_CHECKER="$bin_root/ht-production-trace-check"
    export KM_HT_TEST_LEAN_PRODUCTION_TRACE_CHECKER="$bin_root/ht-production-trace-check"
    export KM_HT_LEAN_FINITE_PRODUCTION_TERMINAL_CHECKER="$bin_root/ht-finite-production-terminal-check"
    export KM_HT_TEST_LEAN_FINITE_PRODUCTION_TERMINAL_CHECKER="$bin_root/ht-finite-production-terminal-check"
    export KM_HT_LEAN_REGULAR_PRODUCTION_TERMINAL_CHECKER="$bin_root/ht-regular-production-terminal-check"
    export KM_HT_TEST_LEAN_REGULAR_PRODUCTION_TERMINAL_CHECKER="$bin_root/ht-regular-production-terminal-check"
    export KM_HT_LEAN_EQUALITY_PRODUCTION_BLOCKING_CHECKER="$bin_root/ht-equality-production-blocking-check"
    export KM_HT_TEST_LEAN_EQUALITY_PRODUCTION_BLOCKING_CHECKER="$bin_root/ht-equality-production-blocking-check"
    export KM_HT_LEAN_EQUALITY_PRODUCTION_TRACE_CHECKER="$bin_root/ht-equality-production-trace-check"
    export KM_HT_TEST_LEAN_EQUALITY_PRODUCTION_TRACE_CHECKER="$bin_root/ht-equality-production-trace-check"
    export KM_HT_LEAN_EQUALITY_PRODUCTION_TERMINAL_CHECKER="$bin_root/ht-equality-production-terminal-check"
    export KM_HT_TEST_LEAN_EQUALITY_PRODUCTION_TERMINAL_CHECKER="$bin_root/ht-equality-production-terminal-check"
    export KM_HT_TEST_LEAN_CARDINALITY_FRONTIER_CHECKER="$bin_root/ht-cardinality-frontier-check"
    export KM_HT_TEST_LEAN_ROOTED_CARDINALITY_FRONTIER_CHECKER="$bin_root/ht-rooted-cardinality-frontier-check"
    export KM_HT_TEST_LEAN_NATIVE_ABOX_TAXONOMY_MATRIX_CHECKER="$bin_root/ht-native-abox-taxonomy-matrix-cert-check"
    export KM_HT_TEST_LEAN_NATIVE_ABOX_CARDINALITY_TAXONOMY_MATRIX_CHECKER="$bin_root/ht-native-abox-cardinality-taxonomy-cert-check"
    export KM_HT_TEST_LEAN_NATIVE_ABOX_TAXONOMY_SOURCE_CHECKER="$bin_root/ht-native-abox-taxonomy-source-cert-check"
    export KM_HT_TEST_LEAN_NATIVE_ABOX_CARDINALITY_TAXONOMY_SOURCE_CHECKER="$bin_root/ht-native-abox-cardinality-taxonomy-source-cert-check"
    export KM_HT_TEST_LEAN_JOINT_NATIVE_ABOX_CLASSIFICATION_CHECKER="$bin_root/ht-joint-native-abox-classification-cert-check"

    cargo test --release equality_decision_pairwise_blocks_and_checks_a_satisfiable_cycle -- --nocapture
    cargo test --release equality_production_blocking_checks_rejection_provenance -- --nocapture
    cargo test --release native_abox_production_blocking_checks_joint_rejection_provenance -- --nocapture
    cargo test --release equality_and_cardinality_folds_copy_incoming_blocker_edges -- --nocapture
    cargo test --release equality_free_refutation_pairwise_blocks_a_satisfiable_cycle -- --nocapture
    cargo test --release cardinality_doubling_histories_reject_stale_single_and_multi_root_rounds -- --nocapture
    cargo test --release cardinality_decision_emits_sat_or_unsat_checker_ready_evidence -- --nocapture
    cargo test --release native_abox_cardinality_global_decision_uses_joint_wire -- --nocapture
    cargo test --release source_matrix_passes_real_lean_checker -- --nocapture
    cargo test --release certified_input_coverage_matches_the_lean_truth_table -- --nocapture
    cargo test --release regular_certificate_serializes_general_guarded_residual_bodies -- --nocapture
    cargo test --release --test ht_taxonomy_certificate -- --nocapture
)
