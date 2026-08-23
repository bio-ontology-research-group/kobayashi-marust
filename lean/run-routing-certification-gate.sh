#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
lean_root="$repo_root/lean"
engine_root="$repo_root/engine"
bin_path="$lean_root/.lake/build/bin/km-automatic-routing-check"
target_root="$repo_root/.work/target"
artifact_root="$repo_root/.work/artifacts"
surface_log="$artifact_root/routing-certification-surface.log"
lean_threads=${KM_CERT_LEAN_THREADS:-4}

mkdir -p "$artifact_root"

preflight="$repo_root/tools/workspace-preflight.sh"
if [[ -x "$preflight" ]]; then
    "$preflight"
else
    /home/leechuck/Public/software/kobayashi-marust/tools/workspace-preflight.sh
fi

cleanup_checker() {
    [[ "${KM_CERT_KEEP_NATIVE_CHECKERS:-0}" == "1" ]] && return
    [[ ! -e "$bin_path" ]] || unlink "$bin_path"
}
trap cleanup_checker EXIT

(
    cd "$lean_root"
    LEAN_NUM_THREADS="$lean_threads" lake build \
        ContextCalculus.CertifiedRouting \
        ContextCalculus.KMAutomaticRouting \
        ContextCalculus.KMAutomaticSupervisor \
        ContextCalculus.KMWorkerPublication \
        ContextCalculus.ELCheckerTermEmbedding \
        ContextCalculus.HTCheckerTermEmbedding \
        ContextCalculus.HTDirectCommonSourceWire \
        ContextCalculus.HTSkolemPairCheckerTermEmbedding \
        ContextCalculus.HTMixedCommonSourceWire \
        ContextCalculus.HTSkolemBundleCheckerTermEmbedding \
        ContextCalculus.HTBundleCommonSourceWire \
        ContextCalculus.HTCardinalityCheckerTermEmbedding \
        ContextCalculus.HTDirectCardinalityCommonSourceWire \
        ContextCalculus.HTMixedCardinalityCommonSourceWire \
        ContextCalculus.HTRoutingSource \
        km-automatic-routing-check 2>&1 | tee "$surface_log"
)

if grep -q 'sorryAx' "$surface_log"; then
    echo "routing certification surface depends on an admitted theorem" >&2
    exit 1
fi

for theorem in \
    SourceBoundWorker.erase_soundAt \
    SourceBoundWorker.liftTranslation \
    SourceBoundWorker.liftTranslation_completeAt \
    WirePublication.check_sound \
    WireJointNativeABoxClassification.check_sound \
    models_encode_iff \
    entailsSub_encode_iff \
    WireDirectCommonSource.check_sound \
    entailsSub_mixed_encode_iff \
    WireMixedCommonSource.check_sound \
    entailsSub_bundles_encode_iff \
    WireBundleCommonSource.check_sound \
    models_minimumClauses_iff \
    valid_maximumClause_iff \
    models_pairClauses_iff \
    models_cardinalityClauses_fixed_iff \
    models_cardinalityClauses_implies_projected \
    projected_implies_exists_cardinalityClauses_model \
    entailsSub_cardinalityClauses_iff \
    modelsProjectedDefs_map_natInterp \
    modelsProjectedDefs_map_finInterp \
    WireDirectCardinalityCommonSource.check_sound \
    valid_shiftClauseFunctions_iff \
    models_shiftOntologyFunctions_iff \
    functionView_mergedModel \
    WireMixedCardinalityCommonSource.check_sound \
    Source.entailsSub_iff_target \
    CardinalitySource.entailsSub_iff_target \
    AutomaticRouter.sound_and_complete \
    WireSelection.check_sound \
    automatic_specialist_decline_has_coverage \
    CertifiedSupervisor.sound_and_complete
do
    grep -q "$theorem" "$surface_log" || {
        echo "missing routing certification-surface axiom audit: $theorem" >&2
        exit 1
    }
done

"$bin_path" "$lean_root/testdata/km-routing-large-horn-valid.json"
if "$bin_path" "$lean_root/testdata/km-routing-large-horn-forged.json"; then
    echo "forged automatic routing decision was accepted" >&2
    exit 1
fi

(
    cd "$engine_root"
    CARGO_TARGET_DIR="$target_root" cargo test --release \
        routing::tests::large_horn_functional_terminology_retains_exact_fallback
    CARGO_TARGET_DIR="$target_root" cargo test --release \
        routing::tests::automatic_atomic_declines_retain_source_appropriate_fallbacks
    CARGO_TARGET_DIR="$target_root" cargo test --release --test elc_certificate \
        automatic_el_decline_retries_exactly_but_forced_el_remains_atomic
)

echo "routing certification gate passed"
