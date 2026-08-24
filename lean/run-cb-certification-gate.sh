#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
lean_root="$repo_root/lean"
engine_root="$repo_root/engine"
bin_root="$lean_root/.lake/build/bin"
target_root="$repo_root/.work/target"
artifact_root="$repo_root/.work/artifacts"
surface_log="$artifact_root/cb-certification-surface.log"
lean_threads=${KM_CERT_LEAN_THREADS:-4}

mkdir -p "$artifact_root"

preflight="$repo_root/tools/workspace-preflight.sh"
if [[ -x "$preflight" ]]; then
    "$preflight"
else
    /home/leechuck/Public/software/kobayashi-marust/tools/workspace-preflight.sh
fi

mapfile -t checkers < <(
    awk '
        /^name = "cb-/ {
            value = $3
            gsub(/"/, "", value)
            print value
        }
    ' "$lean_root/lakefile.toml" | sort -u
)

# The manifest is authoritative. Every native CB checker is built by this gate,
# so adding a checker cannot silently leave it outside release validation.
(( ${#checkers[@]} > 0 )) || {
    echo "CB certification gate found no native checkers" >&2
    exit 1
}

# These statically linked executables are disposable gate products and can
# collectively occupy many gigabytes. Preserve the proof-library cache, but
# reclaim the checker binaries on exit unless explicitly retained for audit.
cleanup_native_checkers() {
    [[ "${KM_CERT_KEEP_NATIVE_CHECKERS:-0}" == "1" ]] && return
    local checker
    for checker in "${checkers[@]}"; do
        [[ ! -e "$bin_root/$checker" ]] || unlink "$bin_root/$checker"
    done
}
trap cleanup_native_checkers EXIT

(
    cd "$lean_root"
    LEAN_NUM_THREADS="$lean_threads" lake build
    LEAN_NUM_THREADS="$lean_threads" lake build "${checkers[@]}"
    LEAN_NUM_THREADS="$lean_threads" lake build ContextCalculus.CBCertificationSurface \
        2>&1 | tee "$surface_log"
)

if grep -q 'sorryAx' "$surface_log"; then
    echo "CB certification surface depends on an admitted theorem" >&2
    exit 1
fi

surface_theorems=(
    certifiedCBGlobalProductionClosure
    certifiedCBClashFreeGlobalProductionModel
    certifiedCBStandaloneContextProof
    certifiedCBSourceLiveProductionDerivation
    certifiedCBSourceLocalClosure
    certifiedCBSourceHyperClosure
    certifiedCBSourceJoin3Closure
    certifiedCBSharedProductionTaxonomyPublication
    certifiedCBExactTaxonomyPublication
    certifiedCBSourceExactTaxonomyPublication
    certifiedCBProductionExactTaxonomyPublication
)
for theorem in "${surface_theorems[@]}"; do
    grep -q "CBCertificationSurface.*$theorem" "$surface_log" || {
        echo "missing CB certification-surface axiom audit: $theorem" >&2
        exit 1
    }
done

"$bin_root/cb-standalone-context-proof-check" \
    "$lean_root/testdata/cb-standalone-context-pred-valid.json"
if "$bin_root/cb-standalone-context-proof-check" \
    "$lean_root/testdata/cb-standalone-context-forward-ref-forged.json"; then
    echo "forged forward-reference CB context proof was accepted" >&2
    exit 1
fi

for checker in "${checkers[@]}"; do
    [[ -x "$bin_root/$checker" ]] || {
        echo "missing Lean checker: $bin_root/$checker" >&2
        exit 1
    }
done

(
    cd "$engine_root"
    export CARGO_TARGET_DIR="$target_root"
    export KM_CB_TEST_SOURCE_EXACT_TAXONOMY_CHECKER="$bin_root/cb-source-taxonomy-cert-check"
    export KM_CB_TEST_STANDALONE_CONTEXT_PROOF_CHECKER="$bin_root/cb-standalone-context-proof-check"
    export KM_CB_TEST_SOURCE_PRODUCTION_TAXONOMY_CHECKER="$bin_root/cb-source-production-taxonomy-check"
    export KM_CB_TEST_REGULAR_ARBITRARY_CHAIN_CHECKER="$bin_root/cb-regular-arbitrary-chain-countermodel-check"
    export KM_CB_TEST_TYPED_REGULAR_ARBITRARY_CHAIN_CHECKER="$bin_root/cb-typed-regular-arbitrary-chain-countermodel-check"
    export KM_CB_TEST_PRED_SEND_COVERAGE_CHECKER="$bin_root/cb-pred-send-coverage-check"
    export KM_CB_TEST_SOURCE_LIVE_DERIVATION_CHECKER="$bin_root/cb-source-live-insertion-derivation-check"
    export KM_CB_TEST_SOURCE_LOCAL_CLOSURE_CHECKER="$bin_root/cb-source-local-closure-check"
    export KM_CB_TEST_SOURCE_HYPER_CLOSURE_CHECKER="$bin_root/cb-source-hyper-closure-check"
    export KM_CB_TEST_SOURCE_JOIN3_CLOSURE_CHECKER="$bin_root/cb-source-join3-closure-check"
    # Legacy fixture processes still load handcrafted source documents from
    # files. Production certified execution has no such escape hatch.
    export KM_CB_TEST_ALLOW_EXTERNAL_SOURCE=1

    cargo test --test cb_live_state
    cargo test --lib certified_typed_source
    cargo test --lib source_exact_taxonomy_uses_real_production_traces_and_models
    cargo test --lib pred_standalone_dag_passes_the_real_lean_checker
    cargo test --lib native_source_live_pred_candidate_passes_real_lean_checker
    cargo test --lib native_regular_countermodel_passes_the_exact_lean_wire_checker
    cargo test --lib typed_regular_cardinality_countermodel_respects_function_allocation
    cargo test --lib native_pred_send_candidate_passes_real_lean_checker
    cargo test --lib native_root_pred_send_candidate_passes_real_lean_checker
)

echo "CB certification gate passed"
