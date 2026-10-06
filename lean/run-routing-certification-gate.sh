#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
lean_root="$repo_root/lean"
engine_root="$repo_root/engine"
bin_path="$lean_root/.lake/build/bin/km-automatic-routing-check"
work_root="${KM_WORK_ROOT:-$repo_root/.work}"
target_root="$work_root/target"
artifact_root="$work_root/artifacts"
surface_log="$artifact_root/routing-certification-surface.log"
lean_threads=${KM_CERT_LEAN_THREADS:-1}
lean_cpuset=${KM_CERT_LEAN_CPUSET:-0-3}

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
    LEAN_NUM_THREADS="$lean_threads" taskset -c "$lean_cpuset" lake build \
        ContextCalculus.CertifiedRouting \
        ContextCalculus.KMAutomaticRouting \
        ContextCalculus.KMAutomaticSupervisor \
        ContextCalculus.KMWorkerPublication \
        ContextCalculus.KMCommonRoutingSource \
        ContextCalculus.KMConcreteWorkerAdapters \
        ContextCalculus.KMConcreteAutomaticSupervisor \
        ContextCalculus.KMIncrementalExplanationCertification \
        ContextCalculus.IncrementalHornActivation \
        ContextCalculus.IncrementalSourceLocality \
        ContextCalculus.KMAtomicABoxPublication \
        ContextCalculus.ABoxBooleanInclusion \
        ContextCalculus.EndpointTransitivity \
        ContextCalculus.EndpointRoleHierarchy \
        ContextCalculus.GuardedTransitivity \
        ContextCalculus.AbsorbingTransitivity \
        ContextCalculus.DLSafeAtomicTaxonomyExtension \
        ContextCalculus.DLSafeRuleJoinOrdering \
        ContextCalculus.DLSafeGroundRuleNormalization \
        ContextCalculus.InverseRoleChainNormalization \
        ContextCalculus.NativeCardinalityNormalization \
        ContextCalculus.ELCheckerTermEmbedding \
        ContextCalculus.ELNormalCheckerTermEmbedding \
        ContextCalculus.ELCommonSourceWire \
        ContextCalculus.HTCheckerTermEmbedding \
        ContextCalculus.HTDirectCommonSourceWire \
        ContextCalculus.HTDirectTaxonomyCommonPublication \
        ContextCalculus.HTMixedTaxonomyCommonPublication \
        ContextCalculus.HTBundleTaxonomyCommonPublication \
        ContextCalculus.HTSkolemPairCheckerTermEmbedding \
        ContextCalculus.HTMixedCommonSourceWire \
        ContextCalculus.HTSkolemBundleCheckerTermEmbedding \
        ContextCalculus.HTBundleCommonSourceWire \
        ContextCalculus.HTCardinalityCheckerTermEmbedding \
        ContextCalculus.HTDirectCardinalityCommonSourceWire \
        ContextCalculus.HTMixedCardinalityCommonSourceWire \
        ContextCalculus.HTBundleCardinalityCommonSourceWire \
        ContextCalculus.HTCommonRoutingWire \
        ContextCalculus.HTRoutingSource \
        km-automatic-routing-check 2>&1 | tee "$surface_log"
)

if grep -q 'sorryAx' "$surface_log"; then
    echo "routing certification surface depends on an admitted theorem" >&2
    exit 1
fi

for theorem in \
    IncrementalHornActivation.derives_bounded \
    IncrementalHornActivation.transfer_inactive_removed \
    IncrementalHornActivation.inactive_delta_preserves_closure \
    IncrementalHornActivation.entails_iff_derives \
    IncrementalHornActivation.inactive_delta_preserves_entailment \
    IncrementalSourceLocality.eval_mask \
    IncrementalSourceLocality.transfer_model \
    IncrementalSourceLocality.inactive_delta_preserves_subsumptions \
    IncrementalSourceLocality.inactive_delta_preserves_query_satisfiability \
    ABoxBooleanInclusion.union_operand_included \
    ABoxBooleanInclusion.intersection_operand_included \
    ABoxBooleanInclusion.equivalence_directions \
    ABoxBooleanInclusion.inclusion_transitive \
    ABoxBooleanInclusion.asserted_disjoint_clash \
    ABoxBooleanInclusion.inconsistent_subset \
    EndpointTransitivity.reach_transitive \
    EndpointTransitivity.domain_preserved \
    EndpointTransitivity.range_preserved \
    EndpointTransitivity.transitive_model_extension \
    EndpointTransitivity.reach_inclusion \
    EndpointTransitivity.reach_inverse_inclusion \
    EndpointTransitivity.selective_inclusion \
    EndpointTransitivity.selective_inverse_inclusion \
    EndpointTransitivity.recognition_reaches \
    EndpointTransitivity.guarded_consumer_preserved \
    EndpointTransitivity.recognition_extension \
    EndpointTransitivity.left_reach_absorption \
    EndpointTransitivity.left_absorption_reach_target \
    EndpointTransitivity.left_absorption_both_reach \
    EndpointTransitivity.selective_left_absorption \
    NativeCardinalityNormalization.minimum_definition_extension_iff \
    NativeCardinalityNormalization.maximum_definition_extension_iff \
    DLSafeAtomicTaxonomyExtension.boolean_query_projection_exact \
    DLSafeAtomicTaxonomyExtension.guarded_named_rules_preserved \
    DLSafeAtomicTaxonomyExtension.role_chain_preserved \
    DLSafeRuleJoinOrdering.reject_false_premise \
    DLSafeRuleJoinOrdering.accept_true_head \
    DLSafeRuleJoinOrdering.class_domain_restriction \
    DLSafeGroundRuleNormalization.ground_atom_exact \
    DLSafeGroundRuleNormalization.grounded_rule_exact \
    DLSafeGroundRuleNormalization.ground_family_extension_iff \
    InverseRoleChainNormalization.theory_consequences_preserved \
    InverseRoleChainNormalization.centered_binary_chain \
    InverseRoleChainNormalization.reciprocal_bridges_preserve_transitivity \
    SQWRLClassificationProjection.models_preserved \
    DLSafeEmptyNamedDomain.guarded_rule_vacuous \
    DLSafeEmptyNamedDomain.theory_models_preserved \
    DLSafeEmptyNamedDomain.rule_family_models_preserved \
    SQWRLClassificationProjection.consequences_preserved \
    SQWRLClassificationProjection.mixed_rule_preserved \
    SourceBoundWorker.erase_soundAt \
    SourceBoundWorker.liftTranslation \
    SourceBoundWorker.liftTranslation_completeAt \
    WirePublication.check_sound \
    WireJointNativeABoxClassification.check_sound \
    models_encode_iff \
    models_encodeResidual_iff \
    commonResidualEntails_iff_raw \
    models_encodeNormalOntology_modelOfNormalAndRaw \
    commonCombinedEntails_iff_elcSource \
    commonMappedCombinedEntails_iff_finite \
    finiteELCSourceEntails_iff_publicationSource \
    WireCertificate.check_common_source_sound \
    WireCertificate.check_common_routing_source_sound \
    elcWireEntails_iff \
    elcBit_exact \
    elcAnswer_correct \
    elcCheck_correct \
    elcAccept_sound \
    ELCExecution.worker_soundAt \
    finTaxonomyAnswer_correct \
    finBooleanAnswer_correct \
    directHTAnswer_correct \
    directHTCheck_correct \
    directHTAccept_sound \
    DirectHTExecution.worker_soundAt \
    mixedHTAnswer_correct \
    mixedHTCheck_correct \
    mixedHTAccept_sound \
    MixedHTExecution.worker_soundAt \
    bundleHTAnswer_correct \
    bundleHTCheck_correct \
    bundleHTAccept_sound \
    BundleHTExecution.worker_soundAt \
    exactCardinalityBit_exact \
    directCardinalityHTAnswer_correct \
    directCardinalityHTCheck_correct \
    directCardinalityHTAccept_sound \
    DirectCardinalityHTExecution.worker_soundAt \
    mixedCardinalityHTAnswer_correct \
    mixedCardinalityHTCheck_correct \
    mixedCardinalityHTAccept_sound \
    MixedCardinalityHTExecution.worker_soundAt \
    bundleCardinalityHTAnswer_correct \
    bundleCardinalityHTCheck_correct \
    bundleCardinalityHTAccept_sound \
    BundleCardinalityHTExecution.worker_soundAt \
    htAccept_sound \
    HTExecution.worker_soundAt \
    kmExactAccept_sound \
    KMExactExecution.worker_soundAt \
    requestedExactAccept_sound \
    KMRequestedExecution.worker_soundAt \
    KMRequestedExecution.certifiedProcedure \
    ConcreteSupervisor.certified \
    ConcreteSupervisor.sound_and_complete \
    ConcreteSupervisor.profile_independent_sound \
    IncrementalRevisionPublication.exact \
    CheckedCell.answer_iff_entails \
    CheckedCell.entailed \
    CheckedCell.notEntailed \
    entails_mono \
    CertifiedExplanation.entails \
    CertifiedExplanation.oneDeletionMinimal \
    CertifiedExplanation.subsetMinimal \
    CheckedGlobal.inconsistent \
    CheckedGlobal.satisfiable \
    satisfiable_of_included \
    CertifiedInconsistencyExplanation.inconsistent \
    CertifiedInconsistencyExplanation.subsetMinimal \
    singleClass_of_oneClass \
    conflicting_rows_decline \
    singleClass_map_of_injective \
    atomicSatisfiable_of_singleClass \
    atomicSatisfiable_iff_classes \
    nativeAtomic_models \
    nativeAtomic_fullSatisfiable \
    nativeAtomic_taxonomy_exact \
    publish_frontend_false \
    publish_frontend_clash \
    publish_consistent_iff \
    direct_disjoint_assertions_inconsistent \
    entailsSub_encode_iff \
    WireDirectCommonSource.check_sound \
    WireDirectTaxonomyPublication.check_sound \
    directHTCheck_common_routing_source_sound \
    WireMixedTaxonomyPublication.check_sound \
    mixedHTCheck_common_routing_source_sound \
    WireBundleTaxonomyPublication.check_sound \
    bundleHTCheck_common_routing_source_sound \
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
    directCardinalityHTCheck_common_routing_source_sound \
    valid_shiftClauseFunctions_iff \
    models_shiftOntologyFunctions_iff \
    functionView_mergedModel \
    WireMixedCardinalityCommonSource.check_sound \
    mixedCardinalityHTCheck_common_routing_source_sound \
    WireBundleCardinalityCommonSource.check_sound \
    bundleCardinalityHTCheck_common_routing_source_sound \
    cbCheck_common_routing_source_sound \
    cbAccept_sound \
    CBExecution.worker_soundAt \
    WireHTCommonSource.check_sound \
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
    CARGO_TARGET_DIR="$target_root" cargo test --release --lib \
        routing::tests::large_horn_functional_terminology_retains_exact_fallback
    CARGO_TARGET_DIR="$target_root" cargo test --release --lib \
        routing::tests::automatic_atomic_declines_retain_source_appropriate_fallbacks
    CARGO_TARGET_DIR="$target_root" cargo test --release --test elc_certificate \
        automatic_el_decline_retries_exactly_but_forced_el_remains_atomic
    CARGO_TARGET_DIR="$target_root" cargo test --release --lib \
        source_incremental::tests::
    CARGO_TARGET_DIR="$target_root" cargo test --release --lib \
        incremental_activation::tests::
    CARGO_TARGET_DIR="$target_root" cargo test --release --lib \
        frontend::separable_abox_elision_tests::
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
)

echo "routing certification gate passed"
