//! `completion::stubs` — the shared home for not-yet-ported **Algorithm-layer**
//! placeholder marker types referenced by `context.rs` + `algorithm.rs`.
//!
//! KONCLUDE-PORT-NOTE[api]: the completion engine's per-thread context and the
//! task-handle algorithm point at a large family of Algorithm/Strategy/Cache
//! helper classes that are scheduled for later waves (the priority strategies,
//! the dependency/clash factories, the ~14 cache handlers, the 8 satisfiable-task
//! message analysers, the configuration extension). Each is declared here ONCE as
//! a zero-size marker; a pointer field becomes an `Id<Marker>` into its eventual
//! per-thread arena (`Id::NONE` == the C++ `nullptr`), and a by-value member (the
//! analysers) holds the marker struct directly. When a class is really ported it
//! relocates to its own module and these stubs reconcile to it.
//!
//! This is the Algorithm-layer twin of `process::stubs` (the Process-layer queue/
//! hash/linker markers); the two never collide — completion fields that point at
//! a Process-layer container reuse the `process::stubs` markers, while the
//! Algorithm-layer strategies/handlers/factories/analysers live here.

#![allow(dead_code)]

use super::super::cache::context::CacheContext;
use super::super::cache::occstats::{
    OccStatCacheDataId, OccurrenceStatisticsCacheData, OccurrenceStatisticsCacheReader,
    OccurrenceStatisticsCacheWriter, OccurrenceStatisticsConceptData, OccurrenceStatisticsRoleData,
};
use super::super::cache::sigexpand::{
    SigExpanderCacheEntryId, SigExpanderCacheReaderId, SigExpanderEntryWriteDataId,
    SignatureSatisfiableExpanderCache, SignatureSatisfiableExpanderCacheEntryWriteData,
    SignatureSatisfiableExpanderCacheReader, SignatureSatisfiableExpanderCacheValueList,
    SignatureSatisfiableExpanderDepHash,
};
use super::super::cache::value::{CacheValue, CacheValueIdentifier};
use super::super::classifier::{
    deliver_classification_message_data_to_observer,
    is_more_classification_information_required_for_concept,
    ClassificationClassPseudoModelConceptData, ClassificationClassPseudoModelHash,
    ClassificationClassPseudoModelRoleData, ClassificationClassSubsumptionMessageData,
    ClassificationInitializePossibleClassSubsumptionData,
    ClassificationInitializePossibleClassSubsumptionMessageData, ClassificationMessageData,
    ClassificationMessageDataLinker, ClassificationMessageDataObserver,
    ClassificationMessageDataObserverRegistry, ClassificationMessageDataPayload,
    ClassificationMessageDataType, ClassificationPseudoModelIdentifierMessageData,
    ClassificationUpdatePossibleClassSubsumptionMessageData, OptimizedKPSetClassTestingItem,
    OptimizedKPSetClassTestingItemId,
};
use super::super::model::concept::Concept;
use super::super::model::concept_process::{
    ConceptProcessData, ConceptSaturationReferenceLinkingData, SaturationConceptReferenceLinking,
};
use super::super::model::ontology::OntologyArenas;
use super::super::model::op::{
    CCALL, CCAND, CCAQALL, CCAQAND, CCAQCHOOCE, CCAQSOME, CCATLEAST, CCATMOST, CCATOM, CCBRANCHALL,
    CCBRANCHAQALL, CCBRANCHAQAND, CCEQ, CCEQCAND, CCFS_ALL_AQALL_TYPE, CCFS_AQALL_TYPE,
    CCFS_AQAND_TYPE, CCFS_TRIG_TYPE, CCIMPLALL, CCIMPLAQALL, CCIMPLAQAND, CCIMPLTRIG, CCOR, CCSOME,
    CCSUB,
};
use super::super::model::role::Role;
use super::super::model::substrate::{Arena, Cint64, Id, INVALID};
use super::super::model::{ConceptId, RoleId};
use super::super::process::context::ProcessContext;
use super::super::process::dependency::DepKind;
use super::super::process::node::IndividualProcessNode;
use super::super::process::node_resolution::IndividualProcessNodeVector;
use super::super::process::sat_exp_store::IndividualNodeSatisfiableExpandingCacheStoringData;
use super::super::process::sat_node::IndividualSaturationProcessNodeStatusFlags;
use super::super::process::{ConDescId, EdgeId, LabelSetId, NodeId, SatNodeId, TrackPointId};
use super::super::task::adapters::{
    SatisfiableTaskClassificationMessageAdapter, EFEXTRACTIDENTIFIERPSEUDOMODEL,
    EFEXTRACTOTHERNODESMULTIPLEDEPENDENCY, EFEXTRACTOTHERNODESSINGLEDEPENDENCY,
    EFEXTRACTPOSSIBLESUBSUMERSOTHERNODES, EFEXTRACTPOSSIBLESUBSUMERSROOTNODE,
    EFEXTRACTSUBSUMERSOTHERNODES, EFEXTRACTSUBSUMERSROOTNODE,
};
pub use super::computed_cons_handler::ComputedConsequencesCacheHandler;
use super::context::CalculationAlgorithmContext;
pub use super::sat_node_exp_handler::SaturationNodeExpansionCacheHandler;
pub use super::unsat_handler::UnsatisfiableCacheHandler;

/// Port-side carrier for `CPseudoModelAnalyseProcessItem`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PseudoModelAnalyseProcessItem {
    /// `mPseudoModelID`.
    pub pseudo_model_id: Cint64,
    /// `mRootDistance`.
    pub root_distance: Cint64,
    /// `mNodeLinker`; the bool is the Konclude linker negation flag.
    pub nodes: Vec<(NodeId, bool)>,
}

/// Snapshot of the `CReapplyConceptLabelSetIterator` data used by the bounded
/// classification-message analyser helpers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ClassificationAnalyserConceptLabel {
    pub concept: ConceptId,
    pub negated: bool,
    pub branching_tag: Option<Cint64>,
    pub eq_candidate_possible_with_merged_saturated_model: bool,
}

/// Return channels of
/// `testConceptSetWithSaturatedModelMergable`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SaturatedConceptSetMergeResult {
    pub mergable: bool,
    pub clashed: bool,
}

/// Port of `CSaturatedMergedTestItem`.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct SaturatedMergedTestItem {
    pub successfully_merged: bool,
    pub satisfiable_merged: bool,
}

/// Return channels of
/// `checkCanHaveClashWithModel(...)`.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ModelClashCheckResult {
    pub clash_found: bool,
    pub unknown: bool,
    pub clash_free: bool,
}

/// Port-side representation of one recursive
/// `testSaturatedSuccessorModelMergable(...)` call prepared by the
/// multiple-successor merge test.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SaturatedSuccessorMergeJob {
    pub existential_sat_node: SatNodeId,
    pub successor_list: Vec<SatNodeId>,
    pub trivial_successor_propagated_concept_list: Vec<(ConceptId, bool)>,
    pub backward_role_set: std::collections::HashSet<RoleId>,
}

/// Branch selected by
/// `testSaturatedSuccessorModelMergable(...)` after its depth/count gates.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SaturatedSuccessorMergeDispatchKind {
    Single,
    Multiple,
}

/// Port-side call payload for the selected saturated-successor merge helper.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SaturatedSuccessorMergeDispatch {
    pub kind: SaturatedSuccessorMergeDispatchKind,
    pub existential_sat_node: SatNodeId,
    pub successor_list: Vec<SatNodeId>,
    pub trivial_successor_propagated_concept_list: Vec<(ConceptId, bool)>,
    pub backward_role_set: std::collections::HashSet<RoleId>,
    pub remaining_merging_depth: Cint64,
}

/// Initial state prepared by the opening block of
/// `testSingleSaturatedSuccessorModelMergable(...)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SingleSaturatedSuccessorMergeState {
    pub sub_resolved_existential_sat_node: SatNodeId,
    pub saturation_label_set:
        super::super::saturation::satellites::ReapplyConceptSaturationLabelSetId,
    pub successor_influence_concepts: Vec<(RoleId, (ConceptId, bool))>,
}

/// Port of
/// `CSatisfiableTaskClassificationMessageAnalyser::CConceptNegationTriggerItem`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ConceptNegationTriggerItem {
    pub trigger_flag: bool,
    pub negation_flag: bool,
    pub concept: ConceptId,
    pub indi_sat_node: SatNodeId,
}

impl Default for ConceptNegationTriggerItem {
    fn default() -> Self {
        Self {
            trigger_flag: false,
            negation_flag: false,
            concept: ConceptId::NONE,
            indi_sat_node: SatNodeId::NONE,
        }
    }
}

/// Selected analysed concept from the analyser's other-node BFS.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ClassificationAnalyserOtherNodeCandidate {
    pub analyse_concept: ConceptId,
    pub analyse_branch_tag: Cint64,
}

/// Bounded snapshot of an other node considered by the analyser BFS.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClassificationAnalyserOtherNodeSnapshot {
    pub individual_id: Cint64,
    pub is_nominal_individual_node: bool,
    pub has_invalidate_blocker_flags: bool,
    pub has_successor_nominal_connection: bool,
    pub labels: Vec<ClassificationAnalyserConceptLabel>,
    pub single_dependency_label_index: Option<usize>,
    pub successor_individual_ids: Vec<Cint64>,
}

/// Label selected from an other-node snapshot for analyser scheduling.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ClassificationAnalyserOtherNodeVisit {
    pub individual_id: Cint64,
    pub label: ClassificationAnalyserConceptLabel,
    pub is_single_dependency_descriptor: bool,
}

impl ClassificationAnalyserConceptLabel {
    pub fn new(concept: ConceptId, negated: bool, branching_tag: Option<Cint64>) -> Self {
        Self {
            concept,
            negated,
            branching_tag,
            eq_candidate_possible_with_merged_saturated_model: false,
        }
    }

    pub fn new_eq_candidate(
        concept: ConceptId,
        negated: bool,
        branching_tag: Option<Cint64>,
        possible_with_merged_saturated_model: bool,
    ) -> Self {
        Self {
            concept,
            negated,
            branching_tag,
            eq_candidate_possible_with_merged_saturated_model: possible_with_merged_saturated_model,
        }
    }
}

/// Port-side snapshot of
/// `CClassificationSatisfiablePossibleSubsumptionCalculationConceptReferenceLinking`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClassificationAnalyserPossibleSubsumptionState {
    pub possible_subsumption_map_initialized: bool,
    pub remaining_possible_subsumptions: bool,
    pub possible_subsumption_concepts: Vec<ConceptId>,
}

/// Result of the final `analyseSatisfiableTask` message-output tail.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ClassificationAnalyserMessageOutputResult {
    pub had_message_data: bool,
    pub delivered_to_observer: bool,
    pub released_memory_pool: Option<Cint64>,
}

/// Result of Konclude's `getCorrectedIndividualID(...)` helper.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ClassificationAnalyserCorrectedIndividual {
    pub node: NodeId,
    pub individual_id: Cint64,
    pub nondeterministically_merged: bool,
}

/// Bounded result of the root branch in `analyseSatisfiableTask`.
#[derive(Debug, Clone)]
pub struct ClassificationAnalyserRootBranchResult {
    pub corrected_individual: ClassificationAnalyserCorrectedIndividual,
    pub max_deterministic_branch_tag: Cint64,
    pub subsum_message_data_linker: Option<ClassificationMessageDataLinker>,
    pub poss_subsum_message_data_linker: Option<ClassificationMessageDataLinker>,
}

/// Bounded result of composing the analyser root/other-node/pseudomodel/output
/// slices that are live so far.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ClassificationAnalyserBoundedIntegrationResult {
    pub corrected_individual: ClassificationAnalyserCorrectedIndividual,
    pub max_deterministic_branch_tag: Cint64,
    pub other_node_visit_count: usize,
    pub output: ClassificationAnalyserMessageOutputResult,
}

impl ClassificationAnalyserPossibleSubsumptionState {
    pub fn uninitialized() -> Self {
        Self {
            possible_subsumption_map_initialized: false,
            remaining_possible_subsumptions: false,
            possible_subsumption_concepts: Vec::new(),
        }
    }

    pub fn initialized(possible_subsumption_concepts: Vec<ConceptId>) -> Self {
        Self {
            possible_subsumption_map_initialized: true,
            remaining_possible_subsumptions: !possible_subsumption_concepts.is_empty(),
            possible_subsumption_concepts,
        }
    }
}

impl PseudoModelAnalyseProcessItem {
    /// Port of `CPseudoModelAnalyseProcessItem::initPseudoModelAnalyseProcessItem`.
    pub fn init_pseudo_model_analyse_process_item(
        pseudo_model_id: Cint64,
        root_distance: Cint64,
    ) -> Self {
        Self {
            pseudo_model_id,
            root_distance,
            nodes: Vec::new(),
        }
    }

    /// Port of the `CXNegLinker<CIndividualProcessNode*>` append payload.
    pub fn add_node(&mut self, node: NodeId, negated: bool) -> &mut Self {
        self.nodes.push((node, negated));
        self
    }
}

/// Declare zero-size marker structs (used inline as `Id<Marker>` for pointer
/// fields, or held by value for the by-value analyser members).
macro_rules! stub {
    ($($(#[$m:meta])* $name:ident),* $(,)?) => {
        $( $(#[$m])* #[derive(Debug, Default, Clone)] pub struct $name; )*
    };
}

// ===========================================================================
// Priority strategies (`Reasoner/Kernel/Strategy/`).
// ===========================================================================
stub! {
    /// Port of `CConceptProcessingPriorityStrategy`.
    ConceptProcessingPriorityStrategy,
    /// Port of `CIndividualProcessingPriorityStrategy`.
    IndividualProcessingPriorityStrategy,
    /// Port of `CTaskProcessingPriorityStrategy`.
    TaskProcessingPriorityStrategy,
    /// Port of `CUnsatisfiableCacheRetrievalStrategy`.
    UnsatisfiableCacheRetrievalStrategy,
    /// Port of `CIndividualAncestorDepthMaximumConceptProcessingPriorityStrategy`.
    IndividualAncestorDepthMaximumConceptProcessingPriorityStrategy,
}

// ===========================================================================
// Factories / managers (`Reasoner/Kernel/Algorithm/`).
// ===========================================================================
stub! {
    /// Port of `CClashDescriptorFactory`.
    ClashDescriptorFactory,
    /// Port of `CDependencyFactory`.
    DependencyFactory,
    /// Port of `CIndividualNodeManager`.
    IndividualNodeManager,
}

// ===========================================================================
// Cache / expansion handlers (`Reasoner/Kernel/Algorithm/` + `Cache/`).
// ===========================================================================
stub! {
    /// Port of `CCompletionGraphCacheHandler`.
    CompletionGraphCacheHandler,
    /// Port of `CReuseCompletionGraphCacheHandler`.
    ReuseCompletionGraphCacheHandler,
    /// Port of `CConceptNominalSchemaGroundingHandler`.
    ConceptNominalSchemaGroundingHandler,
    /// Port of `CDatatypeIndividualProcessNodeHandler`.
    DatatypeIndividualProcessNodeHandler,
    /// Port of `CIndividualNodeBackendCacheHandler`.
    IndividualNodeBackendCacheHandler,
    /// Port of `CIncrementalCompletionGraphCompatibleExpansionHandler`.
    IncrementalCompletionGraphCompatibleExpansionHandler,
}

/// Live owner of Konclude's ontology-wide satisfiable-expander cache.
///
/// The C++ handler owns one reader, one writer, and a pending write-data chain;
/// the cache itself lives in the reasoner manager.  The bridge is
/// single-threaded, so the Rust port folds those objects into one movable state
/// while retaining the same reader-slot and batched-commit boundaries.
pub struct SatisfiableExpanderCacheHandler {
    pub cache_context: CacheContext,
    pub cache: SignatureSatisfiableExpanderCache,
    pub sat_cache_reader: SigExpanderCacheReaderId,
    pub write_data: SigExpanderEntryWriteDataId,
    write_data_tail: SigExpanderEntryWriteDataId,
    pub stat_retrieval_requests: u64,
    pub stat_signature_hits: u64,
    pub stat_compatible_hits: u64,
    pub stat_satisfiable_hits: u64,
    /// C++ `SATEXPCACHERETRIEVALCOMPATIBILITYTESTCOUNT`.
    pub stat_satisfiable_compatibility_tests: u64,
    /// C++ `SATEXPCACHERETRIEVALCOMPATIBLESATCOUNT`.
    pub stat_compatible_satisfiable_hits: u64,
    /// C++ `SATEXPCACHERETRIEVALINCOMPATIBLESATCOUNT`.
    pub stat_incompatible_satisfiable_hits: u64,
    pub stat_expansion_write_requests: u64,
    pub stat_satisfiable_write_requests: u64,
    pub stat_expansion_writes: u64,
    pub stat_satisfiable_writes: u64,
    pub stat_commit_batches: u64,
}

impl Default for SatisfiableExpanderCacheHandler {
    fn default() -> Self {
        Self::new()
    }
}

impl SatisfiableExpanderCacheHandler {
    pub fn new() -> Self {
        let mut cache_context = CacheContext::new();
        let mut cache = SignatureSatisfiableExpanderCache::new();
        let sat_cache_reader = cache.create_cache_reader(&mut cache_context);
        Self {
            cache_context,
            cache,
            sat_cache_reader,
            write_data: SigExpanderEntryWriteDataId::NONE,
            write_data_tail: SigExpanderEntryWriteDataId::NONE,
            stat_retrieval_requests: 0,
            stat_signature_hits: 0,
            stat_compatible_hits: 0,
            stat_satisfiable_hits: 0,
            stat_satisfiable_compatibility_tests: 0,
            stat_compatible_satisfiable_hits: 0,
            stat_incompatible_satisfiable_hits: 0,
            stat_expansion_write_requests: 0,
            stat_satisfiable_write_requests: 0,
            stat_expansion_writes: 0,
            stat_satisfiable_writes: 0,
            stat_commit_batches: 0,
        }
    }

    pub fn new_with_reader(
        cache_context: CacheContext,
        sat_cache_reader: SigExpanderCacheReaderId,
    ) -> Self {
        Self {
            cache_context,
            cache: SignatureSatisfiableExpanderCache::new(),
            sat_cache_reader,
            write_data: SigExpanderEntryWriteDataId::NONE,
            write_data_tail: SigExpanderEntryWriteDataId::NONE,
            stat_retrieval_requests: 0,
            stat_signature_hits: 0,
            stat_compatible_hits: 0,
            stat_satisfiable_hits: 0,
            stat_satisfiable_compatibility_tests: 0,
            stat_compatible_satisfiable_hits: 0,
            stat_incompatible_satisfiable_hits: 0,
            stat_expansion_write_requests: 0,
            stat_satisfiable_write_requests: 0,
            stat_expansion_writes: 0,
            stat_satisfiable_writes: 0,
            stat_commit_batches: 0,
        }
    }

    fn append_write_data(&mut self, write_data: SigExpanderEntryWriteDataId) {
        if write_data.is_none() {
            return;
        }
        let mut tail = write_data;
        while self
            .cache_context
            .sig_expander_entry_write_data(tail)
            .has_next()
        {
            tail = self
                .cache_context
                .sig_expander_entry_write_data(tail)
                .get_next();
        }
        if self.write_data.is_none() {
            self.write_data = write_data;
        } else {
            self.cache_context
                .sig_expander_entry_write_data_mut(self.write_data_tail)
                .set_next(write_data);
        }
        self.write_data_tail = tail;
    }

    /// Port of `CSatisfiableExpanderCacheHandler::commitCacheMessages`.
    pub fn commit_cache_messages(&mut self) -> bool {
        if self.write_data.is_none() {
            return false;
        }
        let write_data = self.write_data;
        self.write_data = SigExpanderEntryWriteDataId::NONE;
        self.write_data_tail = SigExpanderEntryWriteDataId::NONE;
        self.cache
            .write_cached_data(write_data, 0, &mut self.cache_context);
        // `CWriteCachedDataEvent` transfers a task-owned memory-pool chain to
        // the cache thread; Konclude releases that chain after processing the
        // event.  The cache has copied every accepted value/dependency into
        // persistent entry/linker arenas by this point.  Rewind the three
        // write-message arenas so rejected and consumed messages do not remain
        // ontology-wide for the rest of classification.
        self.cache_context
            .sig_expander_entry_write_datas
            .truncate_to(0);
        self.cache_context
            .sig_expander_cache_value_lists
            .truncate_to(0);
        self.cache_context.sig_expander_dep_hashes.truncate_to(0);
        self.stat_commit_batches += 1;
        true
    }

    fn descriptor_cache_values(
        &self,
        process_context: &ProcessContext,
        ontology: &OntologyArenas,
        individual_node: NodeId,
    ) -> Vec<CacheValue> {
        let label = process_context
            .node(individual_node)
            .use_reapply_con_label_set;
        if label.is_none() {
            return Vec::new();
        }
        let mut descriptors = Vec::new();
        let mut descriptor = process_context
            .label_set(label)
            .get_adding_sorted_concept_description_linker();
        while descriptor.is_some() {
            descriptors.push(descriptor);
            descriptor = process_context
                .con_desc(descriptor)
                .get_next_concept_descriptor();
        }
        // `mAddingSortedConceptDescriptionLinker` is newest first. Konclude
        // prepends while walking it, hence the cache's deterministic linker is
        // oldest first.
        descriptors
            .into_iter()
            .rev()
            .map(|descriptor| {
                let descriptor = process_context.con_desc(descriptor);
                let concept = descriptor.get_concept();
                let identifier = if descriptor.is_negated() {
                    CacheValueIdentifier::CacheValTagAndNegatedConcept
                } else {
                    CacheValueIdentifier::CacheValTagAndConcept
                };
                CacheValue::new_value(
                    ontology.concept(concept).get_concept_tag(),
                    concept.raw,
                    identifier,
                )
            })
            .collect()
    }

    fn cardinality_critical_values(
        &self,
        process_context: &ProcessContext,
        ontology: &OntologyArenas,
        individual_node: NodeId,
    ) -> Vec<CacheValue> {
        let label = process_context
            .node(individual_node)
            .use_reapply_con_label_set;
        if label.is_none() {
            return Vec::new();
        }
        let mut descriptors = Vec::new();
        let mut descriptor = process_context
            .label_set(label)
            .get_adding_sorted_concept_description_linker();
        while descriptor.is_some() {
            descriptors.push(descriptor);
            descriptor = process_context
                .con_desc(descriptor)
                .get_next_concept_descriptor();
        }
        descriptors
            .into_iter()
            .rev()
            .filter_map(|descriptor| {
                let descriptor = process_context.con_desc(descriptor);
                let concept_id = descriptor.get_concept();
                let concept = ontology.concept(concept_id);
                let negated = descriptor.is_negated();
                let operator = concept.get_operator_code();
                if !((!negated && operator == CCATMOST) || (negated && operator == CCATLEAST)) {
                    return None;
                }
                let cardinality = concept.get_parameter() - Cint64::from(negated);
                if cardinality <= 1
                    || process_context
                        .node_role_successor_count(individual_node, concept.get_role())
                        < cardinality
                {
                    return None;
                }
                Some(CacheValue::new_value(
                    concept.get_concept_tag(),
                    concept_id.raw,
                    if negated {
                        CacheValueIdentifier::CacheValTagAndNegatedConcept
                    } else {
                        CacheValueIdentifier::CacheValTagAndConcept
                    },
                ))
            })
            .collect()
    }

    /// Direct port of `isCardinalityRestrictionCriticalForSatisfiable`.
    fn is_cardinality_restriction_critical_for_satisfiable(
        process_context: &ProcessContext,
        ontology: &OntologyArenas,
        individual_node: NodeId,
        descriptor: ConDescId,
    ) -> bool {
        let descriptor = process_context.con_desc(descriptor);
        let concept = ontology.concept(descriptor.get_concept());
        let negated = descriptor.is_negated();
        let operator = concept.get_operator_code();
        if ((!negated && operator == CCATMOST) || (negated && operator == CCATLEAST))
            && concept.get_role().is_some()
        {
            let cardinality = concept.get_parameter() - Cint64::from(negated);
            if cardinality > 1
                && process_context.node_role_successor_count(individual_node, concept.get_role())
                    >= cardinality
            {
                // `hasInverseSubRole` in this Konclude revision returns true.
                return true;
            }
        }
        false
    }

    /// Direct port of `isAutomatConceptRelevantForSatisfiableBranch`.
    fn is_automat_concept_relevant_for_satisfiable_branch(
        ontology: &OntologyArenas,
        concept: ConceptId,
        _negated: bool,
    ) -> bool {
        let concept_ref = ontology.concept(concept);
        let operator = concept_ref.get_concept_operator();
        if operator.has_partial_operator_code_flag(CCFS_AQALL_TYPE) {
            let role = concept_ref.get_role();
            if role.is_some() {
                return ontology
                    .role(role)
                    .get_indirect_super_role_list()
                    .iter()
                    .any(|super_role| super_role.negated);
            }
        } else if operator.has_partial_operator_code_flag(CCFS_AQAND_TYPE) {
            return concept_ref.get_operand_list().iter().any(|operand| {
                Self::is_automat_concept_relevant_for_satisfiable_branch(
                    ontology,
                    operand.target,
                    operand.negated,
                )
            });
        }
        false
    }

    /// Direct port of `isConceptRelevantForSatisfiableBranch`.
    fn is_concept_relevant_for_satisfiable_branch(
        process_context: &mut ProcessContext,
        ontology: &OntologyArenas,
        individual_node: NodeId,
        descriptor: ConDescId,
    ) -> bool {
        let descriptor_ref = process_context.con_desc(descriptor);
        let concept_id = descriptor_ref.get_concept();
        let negated = descriptor_ref.is_negated();
        let concept = ontology.concept(concept_id);
        let operator_code = concept.get_operator_code();
        let concept_operator = concept.get_concept_operator();
        let role = concept.get_role();

        if ((!negated && concept_operator.has_partial_operator_code_flag(CCFS_ALL_AQALL_TYPE))
            || (negated && operator_code == CCSOME))
            && role.is_some()
        {
            // `hasInverseSubRole` returns true in the reference revision.
            return true;
        }

        if ((!negated && operator_code == CCATMOST) || (negated && operator_code == CCATLEAST))
            && role.is_some()
        {
            let cardinality = concept.get_parameter() - Cint64::from(negated);
            return process_context.node_role_successor_count(individual_node, role) >= cardinality;
        }

        if ((!negated
            && (operator_code == CCSOME
                || operator_code == CCAQSOME
                || operator_code == CCATLEAST))
            || (negated && (operator_code == CCALL || operator_code == CCATMOST)))
            && role.is_some()
        {
            let super_roles = ontology.role(role).get_indirect_super_role_list().to_vec();
            for super_role in super_roles {
                if super_role.negated {
                    continue;
                }
                let mut reapply_iterator = process_context.node_role_reapply_iterator(
                    individual_node,
                    super_role.target,
                    false,
                );
                while reapply_iterator.has_next() {
                    let reapply = reapply_iterator.next(process_context, true);
                    if reapply.is_none() {
                        continue;
                    }
                    let reapply_descriptor = process_context
                        .reapply_con_desc(reapply)
                        .get_concept_descriptor();
                    if reapply_descriptor.is_none() {
                        continue;
                    }
                    let reapply_descriptor_ref = process_context.con_desc(reapply_descriptor);
                    let reapply_concept = ontology.concept(reapply_descriptor_ref.get_concept());
                    let reapply_negated = reapply_descriptor_ref.is_negated();
                    let reapply_operator = reapply_concept.get_operator_code();
                    if (reapply_negated && reapply_operator == CCATLEAST)
                        || (!reapply_negated && reapply_operator == CCATMOST)
                    {
                        let cardinality =
                            reapply_concept.get_parameter() - Cint64::from(reapply_negated);
                        if process_context.node_role_successor_count(individual_node, role)
                            >= cardinality
                        {
                            // `hasInverseSubRole(reapplyRole)` returns true.
                            return true;
                        }
                    }
                }
            }
            return false;
        }

        !negated
            && concept_operator.has_partial_operator_code_flag(CCFS_AQAND_TYPE)
            && Self::is_automat_concept_relevant_for_satisfiable_branch(
                ontology, concept_id, negated,
            )
    }

    fn alloc_value_list(
        &mut self,
        values: &[CacheValue],
    ) -> super::super::cache::sigexpand::SigExpanderCacheValueListId {
        let mut list = SignatureSatisfiableExpanderCacheValueList::new();
        for value in values {
            list.append(*value);
        }
        self.cache_context.alloc_sig_expander_cache_value_list(list)
    }

    fn cache_value_for_descriptor(
        process_context: &ProcessContext,
        ontology: &OntologyArenas,
        descriptor: ConDescId,
    ) -> CacheValue {
        let descriptor = process_context.con_desc(descriptor);
        let concept = descriptor.get_concept();
        CacheValue::new_value(
            ontology.concept(concept).get_concept_tag(),
            concept.raw,
            if descriptor.is_negated() {
                CacheValueIdentifier::CacheValTagAndNegatedConcept
            } else {
                CacheValueIdentifier::CacheValTagAndConcept
            },
        )
    }

    fn cache_entry_for_signature(&mut self, signature: Cint64) -> SigExpanderCacheEntryId {
        let mut reader = std::mem::take(
            self.cache_context
                .sig_expander_cache_reader_mut(self.sat_cache_reader),
        );
        let entry = reader.get_cache_entry_by_signature(signature, &mut self.cache_context);
        *self
            .cache_context
            .sig_expander_cache_reader_mut(self.sat_cache_reader) = reader;
        entry
    }

    fn localize_storing_data(
        process_context: &mut ProcessContext,
        individual_node: NodeId,
    ) -> super::super::process::sat_exp_store::IndividualNodeSatisfiableExpandingCacheStoringDataId
    {
        let local = process_context
            .node(individual_node)
            .individual_satisfiable_cache_storing_data(true);
        if local.is_some() {
            return local;
        }
        let previous = process_context
            .node(individual_node)
            .individual_satisfiable_cache_storing_data(false);
        let data = if previous.is_some() {
            process_context.sat_exp_storing_data(previous).clone()
        } else {
            IndividualNodeSatisfiableExpandingCacheStoringData::new()
        };
        let local = process_context.alloc_sat_exp_storing_data(data);
        process_context
            .node_mut(individual_node)
            .set_individual_satisfiable_cache_storing_data(local);
        local
    }

    /// Port of `hasDependencyToAncestor`.
    fn has_dependency_to_ancestor(
        process_context: &ProcessContext,
        individual_node: NodeId,
        mut dep_track_point: TrackPointId,
        branched: &mut bool,
    ) -> bool {
        if dep_track_point.is_none() {
            return true;
        }
        let ancestor_depth = process_context
            .node(individual_node)
            .individual_ancestor_depth();
        let mut seen = std::collections::HashSet::new();
        loop {
            if !seen.insert(dep_track_point) {
                return true;
            }
            let track_point = process_context.track_point(dep_track_point);
            if ancestor_depth <= 0 {
                return process_context
                    .dep_node(track_point.dependency_node())
                    .is_independent_base_dependency_type();
            }
            let dependency_node = process_context.dep_node(track_point.dependency_node());
            let dependency_to_ancestor = if dependency_node.has_appropriate_individual_node() {
                process_context
                    .node(dependency_node.individual_node())
                    .individual_ancestor_depth()
                    < ancestor_depth
            } else {
                false
            };
            if dependency_to_ancestor {
                return true;
            }
            if dependency_node.kind() == DepKind::MergedConcept
                && !dependency_node.has_appropriate_individual_node()
            {
                dep_track_point = dependency_node.previous_dependency_track_point();
                if dep_track_point.is_none() {
                    return true;
                }
                continue;
            }
            if !dependency_node.is_deterministic() {
                *branched = true;
            }
            return false;
        }
    }

    /// Fast path of Konclude's `simpleDependencyTracking`.
    fn simple_dependency_tracking(
        process_context: &ProcessContext,
        ontology: &OntologyArenas,
        individual_node: NodeId,
        concept_tag: Cint64,
        dep_track_point: TrackPointId,
        dep_hash: &mut SignatureSatisfiableExpanderDepHash,
        not_branch_concepts: Option<&std::collections::HashSet<Cint64>>,
        branched: &mut bool,
    ) -> bool {
        if dep_track_point.is_none() {
            return false;
        }
        let track_point = process_context.track_point(dep_track_point);
        let dependency_node = process_context.dep_node(track_point.dependency_node());
        if !dependency_node.is_deterministic() {
            *branched = true;
            return true;
        }
        if dependency_node.is_independent_base_dependency_type() {
            return true;
        }
        if dependency_node.has_additional_dependencies() {
            return false;
        }
        if dependency_node.has_appropriate_individual_node()
            && process_context
                .node(dependency_node.individual_node())
                .individual_ancestor_depth()
                != process_context
                    .node(individual_node)
                    .individual_ancestor_depth()
        {
            return false;
        }
        let dependency_descriptor = dependency_node.concept_descriptor();
        if dependency_descriptor.is_none() {
            return false;
        }
        let dependency_tag = process_context
            .con_desc(dependency_descriptor)
            .get_concept_tag(ontology);
        if not_branch_concepts.is_some_and(|concepts| !concepts.contains(&dependency_tag)) {
            *branched = true;
            return true;
        }
        dep_hash.insert(concept_tag, dependency_tag);
        true
    }

    /// Port of `complexDependencyTracking`.
    fn complex_dependency_tracking(
        process_context: &ProcessContext,
        ontology: &OntologyArenas,
        individual_node: NodeId,
        concept_tag: Cint64,
        initial_track_point: TrackPointId,
        dep_hash: &mut SignatureSatisfiableExpanderDepHash,
        not_branch_concepts: Option<&std::collections::HashSet<Cint64>>,
        branched: &mut bool,
    ) -> bool {
        if initial_track_point.is_none() {
            return false;
        }
        let base_depth = process_context
            .node(individual_node)
            .individual_ancestor_depth();
        let initial = (base_depth, initial_track_point);
        let mut dependencies = std::collections::HashSet::from([initial]);
        let mut pending = std::collections::VecDeque::from([initial]);
        while let Some((ancestor_depth, track_point_id)) = pending.pop_front() {
            if track_point_id.is_none() {
                return false;
            }
            let track_point = process_context.track_point(track_point_id);
            let dependency_node = process_context.dep_node(track_point.dependency_node());
            if !dependency_node.is_deterministic() {
                *branched = true;
                return true;
            }

            let mut new_ancestor_depth = ancestor_depth;
            if dependency_node.has_appropriate_individual_node() {
                new_ancestor_depth = process_context
                    .node(dependency_node.individual_node())
                    .individual_ancestor_depth();
            }
            let mut continue_loading = true;
            if new_ancestor_depth == base_depth {
                let descriptor = dependency_node.concept_descriptor();
                if descriptor.is_some() {
                    let dependency_tag = process_context
                        .con_desc(descriptor)
                        .get_concept_tag(ontology);
                    if not_branch_concepts
                        .is_some_and(|concepts| !concepts.contains(&dependency_tag))
                    {
                        *branched = true;
                        return true;
                    }
                    continue_loading = false;
                    if dependency_tag != concept_tag {
                        dep_hash.insert(concept_tag, dependency_tag);
                    }
                }
            }
            if new_ancestor_depth < base_depth {
                return false;
            }
            if continue_loading {
                let previous = dependency_node.previous_dependency_track_point();
                if previous.is_none() {
                    return false;
                }
                let previous_node = process_context
                    .dep_node(process_context.track_point(previous).dependency_node());
                let next_depth = if previous_node.has_appropriate_individual_node() {
                    process_context
                        .node(previous_node.individual_node())
                        .individual_ancestor_depth()
                } else {
                    new_ancestor_depth
                };
                if dependencies.insert((next_depth, previous)) {
                    pending.push_back((next_depth, previous));
                }
            }

            let mut additional = dependency_node.additional_after_dependencies();
            while additional.is_some() {
                let link = process_context.dep_link(additional);
                let previous = link.previous_dependency_track_point();
                if previous.is_none() {
                    return false;
                }
                // Konclude deliberately keys additional dependencies with the
                // incoming ancestor depth, not the appropriate-node depth.
                if dependencies.insert((ancestor_depth, previous)) {
                    pending.push_back((ancestor_depth, previous));
                }
                additional = link.next_additional_dependency();
            }
        }
        true
    }

    fn queue_expansion_write(
        &mut self,
        previous_signature: Cint64,
        new_signature: Cint64,
        values: &[CacheValue],
        dependency_hash: SignatureSatisfiableExpanderDepHash,
    ) {
        let values = self.alloc_value_list(values);
        let dependency_hash = self
            .cache_context
            .alloc_sig_expander_dep_hash(dependency_hash);
        let mut write = SignatureSatisfiableExpanderCacheEntryWriteData::new();
        write.init_expand_write_data(previous_signature, new_signature, values, dependency_hash);
        let write = self
            .cache_context
            .alloc_sig_expander_entry_write_data(write);
        self.append_write_data(write);
        self.stat_expansion_writes += 1;
    }

    /// Port of the seven-argument `cacheIndividualNodeExpansion` overload.
    fn cache_individual_node_expansion_between(
        &mut self,
        process_context: &mut ProcessContext,
        ontology: &OntologyArenas,
        individual_node: NodeId,
        storing_data: super::super::process::sat_exp_store::IndividualNodeSatisfiableExpandingCacheStoringDataId,
        last_added_descriptor: ConDescId,
        last_cached_descriptor: ConDescId,
        new_signature: Cint64,
        previous_signature: Cint64,
    ) -> bool {
        let mut descriptor = last_added_descriptor;
        let mut values_newest_first = Vec::new();
        let mut dependency_hash = SignatureSatisfiableExpanderDepHash::new();
        let mut directly_branched = false;
        let mut caching_error = false;

        if last_cached_descriptor.is_some() {
            while descriptor != last_cached_descriptor && !directly_branched && !caching_error {
                if descriptor.is_none() {
                    caching_error = true;
                    break;
                }
                let dependency_track_point = process_context
                    .con_desc(descriptor)
                    .get_dependency_track_point();
                let concept_tag = process_context
                    .con_desc(descriptor)
                    .get_concept_tag(ontology);
                if !Self::simple_dependency_tracking(
                    process_context,
                    ontology,
                    individual_node,
                    concept_tag,
                    dependency_track_point,
                    &mut dependency_hash,
                    None,
                    &mut directly_branched,
                ) && !Self::complex_dependency_tracking(
                    process_context,
                    ontology,
                    individual_node,
                    concept_tag,
                    dependency_track_point,
                    &mut dependency_hash,
                    None,
                    &mut directly_branched,
                ) {
                    caching_error = true;
                }
                values_newest_first.push(Self::cache_value_for_descriptor(
                    process_context,
                    ontology,
                    descriptor,
                ));
                descriptor = process_context
                    .con_desc(descriptor)
                    .get_next_concept_descriptor();
            }
        }

        if directly_branched || caching_error {
            let data = process_context.sat_exp_storing_data_mut(storing_data);
            if directly_branched {
                data.set_individual_node_or_successor_branched_concept(true);
            }
            if caching_error {
                data.set_caching_error(true);
            }
            return false;
        }

        while descriptor.is_some() {
            values_newest_first.push(Self::cache_value_for_descriptor(
                process_context,
                ontology,
                descriptor,
            ));
            descriptor = process_context
                .con_desc(descriptor)
                .get_next_concept_descriptor();
        }
        values_newest_first.reverse();
        self.queue_expansion_write(
            previous_signature,
            new_signature,
            &values_newest_first,
            dependency_hash,
        );
        process_context
            .sat_exp_storing_data_mut(storing_data)
            .set_previous_cached(true)
            .set_last_cached_signature(new_signature)
            .set_last_cached_concept_descriptor(last_added_descriptor);
        true
    }

    /// Port of `CSatisfiableExpanderCacheHandler::cacheIndividualNodeExpansion`.
    pub fn cache_individual_node_expansion(
        &mut self,
        process_context: &mut ProcessContext,
        ontology: &OntologyArenas,
        individual_node: NodeId,
    ) -> bool {
        self.stat_expansion_write_requests += 1;
        let label = process_context
            .node(individual_node)
            .use_reapply_con_label_set;
        if label.is_none() {
            return false;
        }
        let signature = process_context
            .label_set(label)
            .get_concept_signature_value();
        let previous_data = process_context
            .node(individual_node)
            .individual_satisfiable_cache_storing_data(false);
        if previous_data.is_some() {
            let data = process_context.sat_exp_storing_data(previous_data);
            if data.has_caching_error()
                || data.has_individual_node_or_successor_branched_concept()
                || data.last_cached_signature() == signature
            {
                return false;
            }
        }
        let storing_data = Self::localize_storing_data(process_context, individual_node);
        let last_added_descriptor = process_context
            .label_set(label)
            .get_adding_sorted_concept_description_linker();
        let (previous_cached, last_cached_descriptor, previous_signature) = {
            let data = process_context.sat_exp_storing_data(storing_data);
            (
                data.has_previous_cached(),
                data.last_cached_concept_descriptor(),
                data.last_cached_signature(),
            )
        };
        if !previous_cached && last_cached_descriptor.is_none() {
            process_context
                .sat_exp_storing_data_mut(storing_data)
                .set_last_cached_concept_descriptor(last_added_descriptor)
                .set_last_cached_signature(signature);
            return true;
        }

        let cached_entry = self.cache_entry_for_signature(signature);
        if cached_entry.is_some() {
            let concept_count = process_context.label_set(label).get_concept_count();
            if self
                .cache_context
                .sig_expander_cache_entry(cached_entry)
                .get_expander_cache_value_count()
                < concept_count
            {
                return false;
            }
            if !self.compare_individual_node_compatibility(
                process_context,
                individual_node,
                cached_entry,
            ) {
                process_context
                    .sat_exp_storing_data_mut(storing_data)
                    .set_caching_error(true);
                return false;
            }
            process_context
                .sat_exp_storing_data_mut(storing_data)
                .set_last_cached_concept_descriptor(last_added_descriptor)
                .set_previous_cached(true)
                .set_last_cached_signature(signature);
            return true;
        }

        let mut directly_branched = false;
        let mut dependency_to_ancestor = false;
        let mut descriptor = last_added_descriptor;
        while descriptor != last_cached_descriptor {
            if descriptor.is_none() {
                process_context
                    .sat_exp_storing_data_mut(storing_data)
                    .set_caching_error(true);
                return false;
            }
            let dependency_track_point = process_context
                .con_desc(descriptor)
                .get_dependency_track_point();
            dependency_to_ancestor |= Self::has_dependency_to_ancestor(
                process_context,
                individual_node,
                dependency_track_point,
                &mut directly_branched,
            );
            descriptor = process_context
                .con_desc(descriptor)
                .get_next_concept_descriptor();
        }
        if dependency_to_ancestor {
            process_context
                .sat_exp_storing_data_mut(storing_data)
                .set_previous_cached(false)
                .set_previous_satisfiable_cached(false)
                .set_last_cached_signature(signature)
                .set_last_cached_concept_descriptor(last_added_descriptor);
            return true;
        }
        if directly_branched {
            process_context
                .sat_exp_storing_data_mut(storing_data)
                .set_individual_node_or_successor_branched_concept(true);
            return false;
        }

        if !previous_cached && last_cached_descriptor.is_some() && previous_signature != 0 {
            self.cache_individual_node_expansion_between(
                process_context,
                ontology,
                individual_node,
                storing_data,
                last_cached_descriptor,
                ConDescId::NONE,
                previous_signature,
                0,
            );
        }
        let can_continue = {
            let data = process_context.sat_exp_storing_data(storing_data);
            !data.has_caching_error() && !data.has_individual_node_or_successor_branched_concept()
        };
        if can_continue {
            self.cache_individual_node_expansion_between(
                process_context,
                ontology,
                individual_node,
                storing_data,
                last_added_descriptor,
                last_cached_descriptor,
                signature,
                previous_signature,
            );
        }
        false
    }

    /// Direct port of
    /// `CSatisfiableExpanderCacheHandler::cacheIndividualNodeSatisfiable`.
    pub fn cache_individual_node_satisfiable(
        &mut self,
        process_context: &mut ProcessContext,
        ontology: &OntologyArenas,
        individual_node: NodeId,
    ) -> bool {
        self.stat_satisfiable_write_requests += 1;
        let label = process_context
            .node(individual_node)
            .use_reapply_con_label_set;
        if label.is_none() {
            return false;
        }
        if process_context
            .label_set(label)
            .concept_structure
            .has_binding_propagation_concepts()
            || process_context
                .label_set(label)
                .concept_structure
                .has_dynamic_created_concepts()
        {
            return false;
        }

        let signature = process_context
            .label_set(label)
            .get_concept_signature_value();
        let previous_data = process_context
            .node(individual_node)
            .individual_satisfiable_cache_storing_data(false);
        if previous_data.is_some() {
            let data = process_context.sat_exp_storing_data(previous_data);
            if data.has_caching_error()
                || (data.has_previous_satisfiable_cached()
                    && data.last_cached_signature() == signature)
            {
                return false;
            }
        }

        let local_data = process_context
            .node(individual_node)
            .individual_satisfiable_cache_storing_data(true);
        if local_data.is_some() && previous_data.is_none() {
            return false;
        }
        let storing_data = Self::localize_storing_data(process_context, individual_node);
        let last_added_descriptor = process_context
            .label_set(label)
            .get_adding_sorted_concept_description_linker();

        let existing = self.cache_entry_for_signature(signature);
        if existing.is_some() {
            if !self.compare_individual_node_compatibility(
                process_context,
                individual_node,
                existing,
            ) {
                process_context
                    .sat_exp_storing_data_mut(storing_data)
                    .set_caching_error(true);
                return false;
            }
            if !self
                .cache_context
                .sig_expander_cache_entry(existing)
                .is_satisfiable()
            {
                let values =
                    self.descriptor_cache_values(process_context, ontology, individual_node);
                let branched_values =
                    self.cardinality_critical_values(process_context, ontology, individual_node);
                let sat_values = self.alloc_value_list(&values);
                let branched_values = self.alloc_value_list(&branched_values);
                let mut sat_write = SignatureSatisfiableExpanderCacheEntryWriteData::new();
                sat_write.init_satisfiable_branch_write_data(
                    signature,
                    sat_values,
                    branched_values,
                );
                let sat_write = self
                    .cache_context
                    .alloc_sig_expander_entry_write_data(sat_write);
                self.append_write_data(sat_write);
                self.stat_satisfiable_writes += 1;
            }
            process_context
                .sat_exp_storing_data_mut(storing_data)
                .set_last_cached_concept_descriptor(last_added_descriptor)
                .set_previous_cached(true)
                .set_previous_satisfiable_cached(true)
                .set_last_cached_signature(signature);
            return true;
        }

        let mut last_cached_descriptor = process_context
            .sat_exp_storing_data(storing_data)
            .last_cached_concept_descriptor();
        let mut descriptors_newest_first = Vec::new();
        let mut directly_branched = false;
        let mut dependency_to_ancestor = false;
        let mut descriptor = last_added_descriptor;
        while descriptor != last_cached_descriptor {
            if descriptor.is_none() {
                process_context
                    .sat_exp_storing_data_mut(storing_data)
                    .set_caching_error(true);
                return false;
            }
            let dependency_track_point = process_context
                .con_desc(descriptor)
                .get_dependency_track_point();
            dependency_to_ancestor |= Self::has_dependency_to_ancestor(
                process_context,
                individual_node,
                dependency_track_point,
                &mut directly_branched,
            );
            descriptors_newest_first.push(descriptor);
            descriptor = process_context
                .con_desc(descriptor)
                .get_next_concept_descriptor();
        }
        if dependency_to_ancestor {
            process_context
                .sat_exp_storing_data_mut(storing_data)
                .set_previous_cached(false)
                .set_previous_satisfiable_cached(false)
                .set_last_cached_signature(0)
                .set_last_cached_concept_descriptor(ConDescId::NONE);
            last_cached_descriptor = ConDescId::NONE;
        }
        if directly_branched {
            process_context
                .sat_exp_storing_data_mut(storing_data)
                .set_individual_node_or_successor_branched_concept(true);
        }
        while descriptor.is_some() {
            descriptors_newest_first.push(descriptor);
            descriptor = process_context
                .con_desc(descriptor)
                .get_next_concept_descriptor();
        }
        descriptors_newest_first.reverse();

        let mut last_signature = process_context
            .sat_exp_storing_data(storing_data)
            .last_cached_signature();
        if !process_context
            .sat_exp_storing_data(storing_data)
            .has_previous_cached()
            && last_cached_descriptor.is_some()
            && last_signature != 0
            && last_signature != signature
        {
            self.cache_individual_node_expansion_between(
                process_context,
                ontology,
                individual_node,
                storing_data,
                last_cached_descriptor,
                ConDescId::NONE,
                last_signature,
                0,
            );
        }

        if !process_context
            .sat_exp_storing_data(storing_data)
            .has_previous_cached()
        {
            last_cached_descriptor = ConDescId::NONE;
            last_signature = 0;
        }

        let mut dependency_hash = SignatureSatisfiableExpanderDepHash::new();
        let mut expansion_values = Vec::new();
        let mut satisfiable_values = Vec::new();
        let mut branched_values = Vec::new();
        let mut last_cached_descriptor_reached = false;
        let mut caching_error = false;
        let mut not_branch_concepts = std::collections::HashSet::new();

        for descriptor in descriptors_newest_first {
            let concept_tag = process_context
                .con_desc(descriptor)
                .get_concept_tag(ontology);
            let mut concept_dependency_branched = false;
            if last_cached_descriptor_reached {
                let dependency_track_point = process_context
                    .con_desc(descriptor)
                    .get_dependency_track_point();
                if !Self::simple_dependency_tracking(
                    process_context,
                    ontology,
                    individual_node,
                    concept_tag,
                    dependency_track_point,
                    &mut dependency_hash,
                    Some(&not_branch_concepts),
                    &mut concept_dependency_branched,
                ) && !Self::complex_dependency_tracking(
                    process_context,
                    ontology,
                    individual_node,
                    concept_tag,
                    dependency_track_point,
                    &mut dependency_hash,
                    Some(&not_branch_concepts),
                    &mut concept_dependency_branched,
                ) {
                    caching_error = true;
                }
            }

            let cache_value =
                Self::cache_value_for_descriptor(process_context, ontology, descriptor);
            let add_to_branched_values = if concept_dependency_branched {
                Self::is_concept_relevant_for_satisfiable_branch(
                    process_context,
                    ontology,
                    individual_node,
                    descriptor,
                )
            } else {
                not_branch_concepts.insert(concept_tag);
                expansion_values.push(cache_value);
                satisfiable_values.push(cache_value);
                Self::is_cardinality_restriction_critical_for_satisfiable(
                    process_context,
                    ontology,
                    individual_node,
                    descriptor,
                )
            };
            if add_to_branched_values {
                branched_values.push(cache_value);
            }
            directly_branched |= concept_dependency_branched;

            if !last_cached_descriptor_reached && descriptor == last_cached_descriptor {
                last_cached_descriptor_reached = true;
            }
        }

        if caching_error {
            process_context
                .sat_exp_storing_data_mut(storing_data)
                .set_caching_error(true);
            return false;
        }

        let mut previous_signature = last_signature;
        if !process_context
            .sat_exp_storing_data(storing_data)
            .has_previous_satisfiable_cached()
            && last_signature == signature
        {
            previous_signature = 0;
        }
        self.queue_expansion_write(
            previous_signature,
            signature,
            &expansion_values,
            dependency_hash,
        );
        let satisfiable_values = self.alloc_value_list(&satisfiable_values);
        let branched_values = self.alloc_value_list(&branched_values);
        let mut satisfiable_write = SignatureSatisfiableExpanderCacheEntryWriteData::new();
        satisfiable_write.init_satisfiable_branch_write_data(
            signature,
            satisfiable_values,
            branched_values,
        );
        let satisfiable_write = self
            .cache_context
            .alloc_sig_expander_entry_write_data(satisfiable_write);
        self.append_write_data(satisfiable_write);
        self.stat_satisfiable_writes += 1;

        process_context
            .sat_exp_storing_data_mut(storing_data)
            .set_previous_cached(true)
            .set_previous_satisfiable_cached(true)
            .set_last_cached_signature(signature)
            .set_last_cached_concept_descriptor(last_added_descriptor)
            .set_individual_node_or_successor_branched_concept(directly_branched);
        true
    }

    /// Port of `CSatisfiableExpanderCacheHandler::isIndividualNodeExpandCached`.
    pub fn is_individual_node_expand_cached(
        &mut self,
        process_context: &ProcessContext,
        individual_node: NodeId,
        satisfiable: Option<&mut bool>,
        entry: Option<&mut SigExpanderCacheEntryId>,
    ) -> bool {
        self.stat_retrieval_requests += 1;
        let con_set = process_context
            .node(individual_node)
            .use_reapply_con_label_set;
        if con_set.is_none() {
            return false;
        }
        let con_set_ref = process_context.label_set(con_set);
        if con_set_ref
            .concept_structure
            .has_binding_propagation_concepts()
            || con_set_ref.concept_structure.has_dynamic_created_concepts()
        {
            return false;
        }

        let con_sig = con_set_ref.get_concept_signature_value();
        let mut sat_cache_reader = std::mem::replace(
            self.cache_context
                .sig_expander_cache_reader_mut(self.sat_cache_reader),
            SignatureSatisfiableExpanderCacheReader::new(),
        );
        let cached_entry =
            sat_cache_reader.get_cache_entry_by_signature(con_sig, &mut self.cache_context);
        *self
            .cache_context
            .sig_expander_cache_reader_mut(self.sat_cache_reader) = sat_cache_reader;
        if cached_entry.is_none() {
            return false;
        }
        self.stat_signature_hits += 1;

        let con_set_count = con_set_ref.get_concept_count();
        let exp_count = self
            .cache_context
            .sig_expander_cache_entry(cached_entry)
            .get_expander_cache_value_count();
        if exp_count < con_set_count {
            return false;
        }

        if !self.compare_individual_node_compatibility(
            process_context,
            individual_node,
            cached_entry,
        ) {
            return false;
        }
        self.stat_compatible_hits += 1;

        if let Some(out) = entry {
            *out = cached_entry;
        }
        let entry_satisfiable = self
            .cache_context
            .sig_expander_cache_entry(cached_entry)
            .is_satisfiable();
        if let Some(out) = satisfiable {
            *out = entry_satisfiable;
        }
        if entry_satisfiable {
            self.stat_satisfiable_hits += 1;
        }
        true
    }

    /// Port of `CSatisfiableExpanderCacheHandler::compareIndividualNodeCompatibility`.
    pub fn compare_individual_node_compatibility(
        &self,
        process_context: &ProcessContext,
        individual_node: NodeId,
        cached_entry: SigExpanderCacheEntryId,
    ) -> bool {
        let con_set = process_context
            .node(individual_node)
            .use_reapply_con_label_set;
        if con_set.is_none() {
            return false;
        }
        let con_set_ref = process_context.label_set(con_set);
        let con_set_count = con_set_ref.get_concept_count();
        let mut exp_cache_value_linker = self
            .cache_context
            .sig_expander_cache_entry(cached_entry)
            .get_expander_cache_value_linker();
        let mut con_nr: Cint64 = 0;

        while exp_cache_value_linker.is_some() && con_nr < con_set_count {
            con_nr += 1;
            let cache_value = self
                .cache_context
                .expander_cache_value_linker(exp_cache_value_linker)
                .get_cache_value();
            let con_tag = cache_value.get_tag();
            let concept = ConceptId::new(cache_value.get_identification());

            let mut con_des = ConDescId::NONE;
            let mut dep_track_point = TrackPointId::NONE;
            if con_set_ref.get_concept_descriptor_by_tag(
                con_tag,
                &mut con_des,
                &mut dep_track_point,
            ) {
                let con_des_ref = process_context.con_desc(con_des);
                let con_negated = con_des_ref.is_negated();
                let cache_negated = cache_value.get_cache_value_identifier()
                    == CacheValueIdentifier::CacheValTagAndNegatedConcept as Cint64;
                if con_negated != cache_negated || con_des_ref.get_concept() != concept {
                    return false;
                }
            } else {
                return false;
            }

            exp_cache_value_linker = self
                .cache_context
                .expander_cache_value_linker(exp_cache_value_linker)
                .get_next();
        }
        true
    }
}

/// Minimal live port of `COccurrenceStatisticsCacheHandler`.
///
/// This keeps the Konclude layering intact for occurrence-stat updates: completion
/// rules call the handler, the handler owns a cache writer, and the writer mutates
/// the F7 `COccurrenceStatisticsCache*` data/vector records in `CacheContext`.
pub struct OccurrenceStatisticsCacheHandler {
    pub cache_context: CacheContext,
    pub cache_data: OccStatCacheDataId,
    pub cache_writer: OccurrenceStatisticsCacheWriter,
    pub ontology_id: Cint64,
}

impl Default for OccurrenceStatisticsCacheHandler {
    fn default() -> Self {
        Self::new()
    }
}

impl OccurrenceStatisticsCacheHandler {
    pub fn new() -> Self {
        let mut cache_context = CacheContext::new();
        let cache_data =
            cache_context.alloc_occ_stat_cache_data(OccurrenceStatisticsCacheData::new());
        let cache_writer = OccurrenceStatisticsCacheWriter::with_cache_data(0, cache_data);
        OccurrenceStatisticsCacheHandler {
            cache_context,
            cache_data,
            cache_writer,
            ontology_id: 0,
        }
    }

    /// Port-facing role-instance increment wrapper used by Unit 35.
    pub fn inc_concept_instance_occurrencce_statistics(
        &mut self,
        concept_id: Cint64,
        concept_count: Cint64,
        role_count: Cint64,
        deterministic_count: Cint64,
        nondeterministic_count: Cint64,
        individual_count: Cint64,
        existential_count: Cint64,
    ) -> &mut Self {
        let concept_vector_count = concept_count.max(concept_id + 1);
        self.cache_writer
            .inc_concept_instance_occurrencce_statistics(
                self.ontology_id,
                concept_vector_count,
                role_count,
                concept_id,
                deterministic_count,
                nondeterministic_count,
                individual_count,
                existential_count,
                &mut self.cache_context,
            );
        self
    }

    /// Port-facing role-instance increment wrapper used by Unit 35.
    pub fn inc_role_instance_occurrencce_statistics(
        &mut self,
        role_id: Cint64,
        concept_count: Cint64,
        role_count: Cint64,
        deterministic_count: Cint64,
        nondeterministic_count: Cint64,
        individual_count: Cint64,
        existential_count: Cint64,
        outgoing_count: Cint64,
        incoming_count: Cint64,
    ) -> &mut Self {
        let role_vector_count = role_count.max(role_id + 1);
        self.cache_writer.inc_role_instance_occurrencce_statistics(
            self.ontology_id,
            concept_count,
            role_vector_count,
            role_id,
            deterministic_count,
            nondeterministic_count,
            individual_count,
            existential_count,
            outgoing_count,
            incoming_count,
            &mut self.cache_context,
        );
        self
    }

    pub fn accummulated_concept_data_occurrence_statistics(
        &mut self,
        concept_id: Cint64,
    ) -> OccurrenceStatisticsConceptData {
        OccurrenceStatisticsCacheReader::with_data(self.cache_data)
            .get_accummulated_concept_data_occurrence_statistics_with_context(
                self.ontology_id,
                concept_id,
                &mut self.cache_context,
            )
    }

    pub fn accummulated_role_data_occurrence_statistics(
        &mut self,
        role_id: Cint64,
    ) -> OccurrenceStatisticsRoleData {
        OccurrenceStatisticsCacheReader::with_data(self.cache_data)
            .get_accummulated_role_data_occurrence_statistics_with_context(
                self.ontology_id,
                role_id,
                &mut self.cache_context,
            )
    }
}

// ===========================================================================
// Context-layer back-references (`Process/` + `Scheduler/` + `Task/`).
// ===========================================================================
stub! {
    /// Port of `CProcessTagger`.
    ProcessTagger,
    /// Port of `CProcessingStatisticGathering`.
    ProcessingStatisticGathering,
}

// `CSatisfiableCalculationTask` is now fully ported in the `task` subtree (W6); the
// completion layer's placeholder marker is replaced by a re-export so every
// `Id<SatisfiableCalculationTask>` in completion points at the real task (carrying
// the 16 adapter handles, incl. the incremental-consistency adapter). Re-aliasing a
// stub onto the real struct is the established reconcile pattern (W2.7 / W3b).
pub use super::super::task::satisfiable_task::SatisfiableCalculationTask;

// ===========================================================================
// Configuration extension (`Task/CCalculationConfigurationExtension`).
// ===========================================================================
stub! {
    /// Port of `CCalculationConfigurationExtension`.
    CalculationConfigurationExtension,
}

// ===========================================================================
// Satisfiable-task message analysers (`Reasoner/Kernel/Algorithm/`).
// KONCLUDE-PORT-NOTE[api]: these are held BY VALUE in the C++ algorithm (not
// pointers); the port holds the zero-size marker by value until they are ported.
// ===========================================================================
stub! {
    /// Port of `CSatisfiableTaskConsistencyPreyingAnalyser`.
    SatisfiableTaskConsistencyPreyingAnalyser,
    /// Port of `CSatisfiableTaskIncrementalConsistencyPreyingAnalyser`.
    SatisfiableTaskIncrementalConsistencyPreyingAnalyser,
    /// Port of `CSatisfiableTaskClassificationMessageAnalyser`.
    SatisfiableTaskClassificationMessageAnalyser,
    /// Port of `CSatisfiableTaskMarkerIndividualPropagationAnalyser`.
    SatisfiableTaskMarkerIndividualPropagationAnalyser,
    /// Port of `CSatisfiableTaskPossibleAssertionCollectingAnalyser`.
    SatisfiableTaskPossibleAssertionCollectingAnalyser,
    /// Port of `CSatisfiableTaskPropertyClassificationMessageAnalyser`.
    SatisfiableTaskPropertyClassificationMessageAnalyser,
    /// Port of `CSatisfiableTaskComplexAnsweringMessageAnalyser`.
    SatisfiableTaskComplexAnsweringMessageAnalyser,
    /// Port of `CSatisfiableTaskPropagationBindingAnsweringMessageAnalyser`.
    SatisfiableTaskPropagationBindingAnsweringMessageAnalyser,
}

impl SatisfiableTaskClassificationMessageAnalyser {
    /// Konclude's hard-coded pseudomodel extraction depth cap.
    pub const MAX_PSEUDO_MODEL_DEPTH: Cint64 = 3;
    /// Konclude's hard-coded pseudomodel extraction node cap.
    pub const MAX_PSEUDO_MODEL_NODES: Cint64 = 30;

    /// Port of
    /// `CSatisfiableTaskClassificationMessageAnalyser::getCorrectedIndividualID`.
    pub fn get_corrected_individual_id(
        &self,
        process_context: &ProcessContext,
        base_individual_node: NodeId,
        individual_node_vector: &IndividualProcessNodeVector,
    ) -> Option<ClassificationAnalyserCorrectedIndividual> {
        if base_individual_node.is_none() {
            return None;
        }

        let base_individual_id = process_context
            .node(base_individual_node)
            .individual_node_id();
        let mut node = individual_node_vector.get_data(base_individual_id);
        if node.is_none() {
            return None;
        }

        let mut nondeterministically_merged = false;
        while process_context
            .node(node)
            .has_merged_into_individual_node_id()
        {
            if !nondeterministically_merged {
                let merge_dep_track_point =
                    process_context.node(node).merged_dependency_track_point();
                if merge_dep_track_point.is_none()
                    || process_context
                        .track_point(merge_dep_track_point)
                        .get_branching_tag()
                        > 0
                {
                    nondeterministically_merged = true;
                }
            }

            let merged_into_id = process_context.node(node).merged_into_individual_node_id();
            node = individual_node_vector.get_data(merged_into_id);
            if node.is_none() {
                return None;
            }
        }

        Some(ClassificationAnalyserCorrectedIndividual {
            node,
            individual_id: process_context.node(node).individual_node_id(),
            nondeterministically_merged,
        })
    }

    /// Bounded port of the root-node branch in
    /// `CSatisfiableTaskClassificationMessageAnalyser::analyseSatisfiableTask`.
    pub fn create_root_classification_message_linkers_from_constructed_node(
        &self,
        adapter: &SatisfiableTaskClassificationMessageAdapter,
        process_context: &ProcessContext,
        constructed_individual_node: NodeId,
        individual_node_vector: &IndividualProcessNodeVector,
        max_deterministic_branch_tag: Cint64,
        possible_subsumption_states: &std::collections::HashMap<
            ConceptId,
            ClassificationAnalyserPossibleSubsumptionState,
        >,
        equivalent_non_candidate_concepts: &std::collections::HashMap<ConceptId, Vec<ConceptId>>,
        concepts: &Arena<Concept>,
    ) -> Option<ClassificationAnalyserRootBranchResult> {
        if adapter.get_testing_concept().is_none() || constructed_individual_node.is_none() {
            return None;
        }

        let corrected_individual = self.get_corrected_individual_id(
            process_context,
            constructed_individual_node,
            individual_node_vector,
        )?;
        let max_deterministic_branch_tag = if corrected_individual.nondeterministically_merged {
            0
        } else {
            max_deterministic_branch_tag
        };

        let consider_root_node = adapter
            .has_extraction_flags(EFEXTRACTSUBSUMERSROOTNODE | EFEXTRACTPOSSIBLESUBSUMERSROOTNODE);
        if !consider_root_node {
            return Some(ClassificationAnalyserRootBranchResult {
                corrected_individual,
                max_deterministic_branch_tag,
                subsum_message_data_linker: None,
                poss_subsum_message_data_linker: None,
            });
        }

        let label_set = process_context
            .node(corrected_individual.node)
            .use_reapply_con_label_set;
        let labels =
            self.extract_classification_analyser_labels_from_label_set(process_context, label_set);

        let mut subsum_message_data_linker = None;
        if adapter.has_extraction_flags(EFEXTRACTSUBSUMERSROOTNODE) {
            subsum_message_data_linker = self.create_root_class_subsumption_message_linker(
                adapter,
                &labels,
                max_deterministic_branch_tag,
                concepts,
            );
        } else {
            let mut message = ClassificationClassSubsumptionMessageData::new();
            message
                .init_classification_subsumption_message_data(adapter.get_testing_concept(), None);
            subsum_message_data_linker = Some(ClassificationMessageDataLinker::from_message(
                ClassificationMessageDataPayload::from_class_subsumption(message),
            ));
        }

        let mut poss_subsum_message_data_linker = None;
        if adapter.has_extraction_flags(EFEXTRACTPOSSIBLESUBSUMERSROOTNODE) {
            for label in &labels {
                if label.negated || !Self::is_named_class(label.concept, concepts) {
                    continue;
                }
                let default_state = ClassificationAnalyserPossibleSubsumptionState::uninitialized();
                let state = possible_subsumption_states
                    .get(&label.concept)
                    .unwrap_or(&default_state);
                let equivalent_non_candidates = equivalent_non_candidate_concepts
                    .get(&label.concept)
                    .map(Vec::as_slice)
                    .unwrap_or(&[]);
                if let Some(poss_payload) = self.create_possible_class_subsumption_message(
                    adapter,
                    label.concept,
                    &labels,
                    state,
                    equivalent_non_candidates,
                    concepts,
                ) {
                    let poss_linker = ClassificationMessageDataLinker::from_message(poss_payload);
                    poss_subsum_message_data_linker = Some(
                        if let Some(existing_linker) = poss_subsum_message_data_linker {
                            poss_linker.append_linker(existing_linker)
                        } else {
                            poss_linker
                        },
                    );
                }
            }
        }

        Some(ClassificationAnalyserRootBranchResult {
            corrected_individual,
            max_deterministic_branch_tag,
            subsum_message_data_linker,
            poss_subsum_message_data_linker,
        })
    }

    /// Live equivalent-non-candidate variant of the root-node analyser branch.
    ///
    /// This keeps the bounded explicit-map helper available, but mirrors
    /// Konclude's live `extractPossibleSubsumptionInformation` call point by
    /// filtering the ontology's equivalent non-candidate set against the current
    /// individual node.
    pub fn create_root_classification_message_linkers_from_constructed_node_with_live_equivalent_non_candidates(
        &self,
        adapter: &SatisfiableTaskClassificationMessageAdapter,
        process_context: &mut ProcessContext,
        ontology: &OntologyArenas,
        constructed_individual_node: NodeId,
        individual_node_vector: &IndividualProcessNodeVector,
        max_deterministic_branch_tag: Cint64,
        possible_subsumption_states: &std::collections::HashMap<
            ConceptId,
            ClassificationAnalyserPossibleSubsumptionState,
        >,
        concepts: &Arena<Concept>,
        roles: &Arena<Role>,
        concept_process_datas: &Arena<ConceptProcessData>,
        concept_reference_linking_datas: &Arena<ConceptSaturationReferenceLinkingData>,
        saturation_concept_reference_linkings: &Arena<SaturationConceptReferenceLinking>,
        ontology_top_concept: Option<ConceptId>,
    ) -> Option<ClassificationAnalyserRootBranchResult> {
        if adapter.get_testing_concept().is_none() || constructed_individual_node.is_none() {
            return None;
        }

        let corrected_individual = self.get_corrected_individual_id(
            process_context,
            constructed_individual_node,
            individual_node_vector,
        )?;
        let max_deterministic_branch_tag = if corrected_individual.nondeterministically_merged {
            0
        } else {
            max_deterministic_branch_tag
        };

        let consider_root_node = adapter
            .has_extraction_flags(EFEXTRACTSUBSUMERSROOTNODE | EFEXTRACTPOSSIBLESUBSUMERSROOTNODE);
        if !consider_root_node {
            return Some(ClassificationAnalyserRootBranchResult {
                corrected_individual,
                max_deterministic_branch_tag,
                subsum_message_data_linker: None,
                poss_subsum_message_data_linker: None,
            });
        }

        let label_set = process_context
            .node(corrected_individual.node)
            .use_reapply_con_label_set;
        let labels =
            self.extract_classification_analyser_labels_from_label_set(process_context, label_set);

        let mut subsum_message_data_linker = None;
        if adapter.has_extraction_flags(EFEXTRACTSUBSUMERSROOTNODE) {
            subsum_message_data_linker = self.create_root_class_subsumption_message_linker(
                adapter,
                &labels,
                max_deterministic_branch_tag,
                concepts,
            );
        } else {
            let mut message = ClassificationClassSubsumptionMessageData::new();
            message
                .init_classification_subsumption_message_data(adapter.get_testing_concept(), None);
            subsum_message_data_linker = Some(ClassificationMessageDataLinker::from_message(
                ClassificationMessageDataPayload::from_class_subsumption(message),
            ));
        }

        let mut poss_subsum_message_data_linker = None;
        if adapter.has_extraction_flags(EFEXTRACTPOSSIBLESUBSUMERSROOTNODE) {
            // Equivalent non-candidate extraction depends on the completed
            // model node, not on the named label whose message we are
            // constructing. Some large KPSet models contain thousands of
            // named labels; repeating the saturation-backed extraction for
            // every label performs the same work thousands of times.
            let (has_equivalent_non_candidates, equivalent_non_candidates) = self
                .collect_equivalent_non_candidate_possible_subsumers(
                    corrected_individual.node,
                    ontology,
                    concepts,
                    roles,
                    concept_process_datas,
                    concept_reference_linking_datas,
                    saturation_concept_reference_linkings,
                    process_context,
                    ontology_top_concept,
                );
            let possible_subsumer_template =
                Self::possible_subsumer_message_template(&labels, concepts);
            let label_tags: std::collections::HashSet<Cint64> = labels
                .iter()
                .map(|label| Self::concept_tag(label.concept, concepts))
                .collect();
            for label in &labels {
                if label.negated || !Self::is_named_class(label.concept, concepts) {
                    continue;
                }
                let default_state = ClassificationAnalyserPossibleSubsumptionState::uninitialized();
                let state = possible_subsumption_states
                    .get(&label.concept)
                    .unwrap_or(&default_state);
                if let Some(poss_payload) = self
                    .create_possible_class_subsumption_message_with_equivalent_non_candidates(
                        adapter,
                        label.concept,
                        &labels,
                        state,
                        has_equivalent_non_candidates,
                        &equivalent_non_candidates,
                        Some(&possible_subsumer_template),
                        Some(&label_tags),
                        concepts,
                    )
                {
                    let poss_linker = ClassificationMessageDataLinker::from_message(poss_payload);
                    poss_subsum_message_data_linker = Some(
                        if let Some(existing_linker) = poss_subsum_message_data_linker {
                            poss_linker.append_linker(existing_linker)
                        } else {
                            poss_linker
                        },
                    );
                }
            }
        }

        Some(ClassificationAnalyserRootBranchResult {
            corrected_individual,
            max_deterministic_branch_tag,
            subsum_message_data_linker,
            poss_subsum_message_data_linker,
        })
    }

    /// Bounded composition of the live classification-message analyser slices.
    pub fn analyse_satisfiable_task_classification_messages_bounded<
        O: ClassificationMessageDataObserver,
    >(
        &self,
        adapter: &SatisfiableTaskClassificationMessageAdapter,
        process_context: &ProcessContext,
        ontology: &OntologyArenas,
        constructed_individual_node: NodeId,
        individual_node_vector: &IndividualProcessNodeVector,
        max_deterministic_branch_tag: Cint64,
        possible_subsumption_states: &std::collections::HashMap<
            ConceptId,
            ClassificationAnalyserPossibleSubsumptionState,
        >,
        equivalent_non_candidate_concepts: &std::collections::HashMap<ConceptId, Vec<ConceptId>>,
        concepts_requiring_more_information: &std::collections::HashSet<ConceptId>,
        other_node_snapshot_nodes: &[NodeId],
        concepts: &Arena<Concept>,
        roles: &Arena<Role>,
        memory_pool: Cint64,
        observer: Option<&mut O>,
    ) -> Option<ClassificationAnalyserBoundedIntegrationResult> {
        let root_result = self.create_root_classification_message_linkers_from_constructed_node(
            adapter,
            process_context,
            constructed_individual_node,
            individual_node_vector,
            max_deterministic_branch_tag,
            possible_subsumption_states,
            equivalent_non_candidate_concepts,
            concepts,
        )?;

        let mut other_node_snapshots = Vec::new();
        for node in other_node_snapshot_nodes {
            if let Some(snapshot) = self
                .extract_other_node_snapshot_from_process_node_resolving_single_dependency(
                    process_context,
                    ontology,
                    *node,
                )
            {
                other_node_snapshots.push(snapshot);
            }
        }

        let mut root_successor_individual_ids = Vec::new();
        let mut succ_it =
            process_context.node_successor_iterator(root_result.corrected_individual.node);
        while succ_it.has_next() {
            let succ_indi_id = succ_it.next_individual_id(true);
            if succ_indi_id != 0 {
                root_successor_individual_ids.push(succ_indi_id);
            }
        }

        let visits = self.collect_other_node_analyse_visits(
            adapter,
            root_result.corrected_individual.individual_id,
            &root_successor_individual_ids,
            &other_node_snapshots,
        );
        let mut analysed_concepts = std::collections::HashSet::new();
        let (other_subsum_linker, other_poss_linker) = self
            .create_other_node_classification_message_linkers(
                adapter,
                adapter.get_testing_concept(),
                &visits,
                &other_node_snapshots,
                concepts_requiring_more_information,
                &mut analysed_concepts,
                possible_subsumption_states,
                equivalent_non_candidate_concepts,
                concepts,
            );

        let subsum_message_data_linker =
            match (other_subsum_linker, root_result.subsum_message_data_linker) {
                (Some(other), Some(root)) => Some(other.append_linker(root)),
                (Some(other), None) => Some(other),
                (None, Some(root)) => Some(root),
                (None, None) => None,
            };
        let poss_subsum_message_data_linker = match (
            other_poss_linker,
            root_result.poss_subsum_message_data_linker,
        ) {
            (Some(other), Some(root)) => Some(other.append_linker(root)),
            (Some(other), None) => Some(other),
            (None, Some(root)) => Some(root),
            (None, None) => None,
        };

        let pm_message_data_linker = self
            .create_pseudo_model_identifier_message_linker_from_base_node(
                adapter,
                process_context,
                root_result.corrected_individual.node,
                root_result.corrected_individual.nondeterministically_merged,
                root_result.max_deterministic_branch_tag,
                concepts,
                roles,
                memory_pool,
            );

        let output = self.deliver_merged_classification_message_data(
            adapter,
            subsum_message_data_linker,
            pm_message_data_linker,
            poss_subsum_message_data_linker,
            memory_pool,
            observer,
        );

        Some(ClassificationAnalyserBoundedIntegrationResult {
            corrected_individual: root_result.corrected_individual,
            max_deterministic_branch_tag: root_result.max_deterministic_branch_tag,
            other_node_visit_count: visits.len(),
            output,
        })
    }

    /// Bounded analyser integration with the classifier-reference lookup kept
    /// inside the analyser path.
    ///
    /// This is the next lifted slice around
    /// `CSatisfiableTaskClassificationMessageAnalyser::analyseSatisfiableTask`:
    /// other-node visits are still bounded to caller-supplied process nodes, but
    /// the "more information required" gate is resolved through the live
    /// classifier reference substrate instead of being supplied as an external
    /// set.
    pub fn analyse_satisfiable_task_classification_messages_with_classifier_references<
        O: ClassificationMessageDataObserver,
    >(
        &self,
        adapter: &SatisfiableTaskClassificationMessageAdapter,
        process_context: &ProcessContext,
        ontology: &OntologyArenas,
        constructed_individual_node: NodeId,
        individual_node_vector: &IndividualProcessNodeVector,
        max_deterministic_branch_tag: Cint64,
        possible_subsumption_states: &std::collections::HashMap<
            ConceptId,
            ClassificationAnalyserPossibleSubsumptionState,
        >,
        equivalent_non_candidate_concepts: &std::collections::HashMap<ConceptId, Vec<ConceptId>>,
        other_node_snapshot_nodes: &[NodeId],
        concepts: &Arena<Concept>,
        concept_process_datas: &Arena<ConceptProcessData>,
        concept_reference_linking_datas: &Arena<ConceptSaturationReferenceLinkingData>,
        testing_items: &[OptimizedKPSetClassTestingItem],
        roles: &Arena<Role>,
        memory_pool: Cint64,
        observer: Option<&mut O>,
    ) -> Option<ClassificationAnalyserBoundedIntegrationResult> {
        let root_result = self.create_root_classification_message_linkers_from_constructed_node(
            adapter,
            process_context,
            constructed_individual_node,
            individual_node_vector,
            max_deterministic_branch_tag,
            possible_subsumption_states,
            equivalent_non_candidate_concepts,
            concepts,
        )?;

        let mut other_node_snapshots = Vec::new();
        for node in other_node_snapshot_nodes {
            if let Some(snapshot) = self
                .extract_other_node_snapshot_from_process_node_resolving_single_dependency(
                    process_context,
                    ontology,
                    *node,
                )
            {
                other_node_snapshots.push(snapshot);
            }
        }

        let mut root_successor_individual_ids = Vec::new();
        let mut succ_it =
            process_context.node_successor_iterator(root_result.corrected_individual.node);
        while succ_it.has_next() {
            let succ_indi_id = succ_it.next_individual_id(true);
            if succ_indi_id != 0 {
                root_successor_individual_ids.push(succ_indi_id);
            }
        }

        let visits = self.collect_other_node_analyse_visits(
            adapter,
            root_result.corrected_individual.individual_id,
            &root_successor_individual_ids,
            &other_node_snapshots,
        );
        let concepts_requiring_more_information = self
            .collect_other_node_concepts_requiring_more_information(
                adapter,
                &visits,
                concepts,
                concept_process_datas,
                concept_reference_linking_datas,
                testing_items,
            );

        self.analyse_satisfiable_task_classification_messages_bounded(
            adapter,
            process_context,
            ontology,
            constructed_individual_node,
            individual_node_vector,
            max_deterministic_branch_tag,
            possible_subsumption_states,
            equivalent_non_candidate_concepts,
            &concepts_requiring_more_information,
            other_node_snapshot_nodes,
            concepts,
            roles,
            memory_pool,
            observer,
        )
    }

    /// Bounded analyser integration with classifier-reference-backed possible
    /// subsumption state extraction.
    ///
    /// This keeps the W238 reference lookup inside the analyser path and also
    /// derives Konclude's `isPossibleSubsumptionMapInitialized()` /
    /// `getClassPossibleSubsumptionMap()` state from the resolved KP-set
    /// classifier item for every root/other-node analysed concept.
    pub fn analyse_satisfiable_task_classification_messages_with_classifier_state<
        O: ClassificationMessageDataObserver,
    >(
        &self,
        adapter: &SatisfiableTaskClassificationMessageAdapter,
        process_context: &ProcessContext,
        ontology: &OntologyArenas,
        constructed_individual_node: NodeId,
        individual_node_vector: &IndividualProcessNodeVector,
        max_deterministic_branch_tag: Cint64,
        equivalent_non_candidate_concepts: &std::collections::HashMap<ConceptId, Vec<ConceptId>>,
        other_node_snapshot_nodes: &[NodeId],
        concepts: &Arena<Concept>,
        concept_process_datas: &Arena<ConceptProcessData>,
        concept_reference_linking_datas: &Arena<ConceptSaturationReferenceLinkingData>,
        testing_items: &[OptimizedKPSetClassTestingItem],
        roles: &Arena<Role>,
        memory_pool: Cint64,
        observer: Option<&mut O>,
    ) -> Option<ClassificationAnalyserBoundedIntegrationResult> {
        let possible_subsumption_states = self
            .collect_possible_subsumption_states_from_classifier_references(
                adapter,
                process_context,
                ontology,
                constructed_individual_node,
                individual_node_vector,
                other_node_snapshot_nodes,
                concepts,
                concept_process_datas,
                concept_reference_linking_datas,
                testing_items,
            )?;

        self.analyse_satisfiable_task_classification_messages_with_classifier_references(
            adapter,
            process_context,
            ontology,
            constructed_individual_node,
            individual_node_vector,
            max_deterministic_branch_tag,
            &possible_subsumption_states,
            equivalent_non_candidate_concepts,
            other_node_snapshot_nodes,
            concepts,
            concept_process_datas,
            concept_reference_linking_datas,
            testing_items,
            roles,
            memory_pool,
            observer,
        )
    }

    fn analyse_satisfiable_task_classification_messages_from_prebuilt_other_node_snapshots<
        O: ClassificationMessageDataObserver,
    >(
        &self,
        adapter: &SatisfiableTaskClassificationMessageAdapter,
        process_context: &ProcessContext,
        ontology: &OntologyArenas,
        constructed_individual_node: NodeId,
        individual_node_vector: &IndividualProcessNodeVector,
        max_deterministic_branch_tag: Cint64,
        possible_subsumption_states: &std::collections::HashMap<
            ConceptId,
            ClassificationAnalyserPossibleSubsumptionState,
        >,
        equivalent_non_candidate_concepts: &std::collections::HashMap<ConceptId, Vec<ConceptId>>,
        concepts_requiring_more_information: &std::collections::HashSet<ConceptId>,
        root_successor_individual_ids: &[Cint64],
        other_node_snapshots: &[ClassificationAnalyserOtherNodeSnapshot],
        concepts: &Arena<Concept>,
        roles: &Arena<Role>,
        memory_pool: Cint64,
        observer: Option<&mut O>,
    ) -> Option<ClassificationAnalyserBoundedIntegrationResult> {
        let root_result = self.create_root_classification_message_linkers_from_constructed_node(
            adapter,
            process_context,
            constructed_individual_node,
            individual_node_vector,
            max_deterministic_branch_tag,
            possible_subsumption_states,
            equivalent_non_candidate_concepts,
            concepts,
        )?;

        let visits = self.collect_other_node_analyse_visits(
            adapter,
            root_result.corrected_individual.individual_id,
            root_successor_individual_ids,
            other_node_snapshots,
        );
        let mut analysed_concepts = std::collections::HashSet::new();
        let (other_subsum_linker, other_poss_linker) = self
            .create_other_node_classification_message_linkers(
                adapter,
                adapter.get_testing_concept(),
                &visits,
                other_node_snapshots,
                concepts_requiring_more_information,
                &mut analysed_concepts,
                possible_subsumption_states,
                equivalent_non_candidate_concepts,
                concepts,
            );

        let subsum_message_data_linker =
            match (other_subsum_linker, root_result.subsum_message_data_linker) {
                (Some(other), Some(root)) => Some(other.append_linker(root)),
                (Some(other), None) => Some(other),
                (None, Some(root)) => Some(root),
                (None, None) => None,
            };
        let poss_subsum_message_data_linker = match (
            other_poss_linker,
            root_result.poss_subsum_message_data_linker,
        ) {
            (Some(other), Some(root)) => Some(other.append_linker(root)),
            (Some(other), None) => Some(other),
            (None, Some(root)) => Some(root),
            (None, None) => None,
        };

        let pm_message_data_linker = self
            .create_pseudo_model_identifier_message_linker_from_base_node(
                adapter,
                process_context,
                root_result.corrected_individual.node,
                root_result.corrected_individual.nondeterministically_merged,
                root_result.max_deterministic_branch_tag,
                concepts,
                roles,
                memory_pool,
            );

        let output = self.deliver_merged_classification_message_data(
            adapter,
            subsum_message_data_linker,
            pm_message_data_linker,
            poss_subsum_message_data_linker,
            memory_pool,
            observer,
        );

        Some(ClassificationAnalyserBoundedIntegrationResult {
            corrected_individual: root_result.corrected_individual,
            max_deterministic_branch_tag: root_result.max_deterministic_branch_tag,
            other_node_visit_count: visits.len(),
            output,
        })
    }

    /// Live other-node traversal wrapper for the classifier-state analyser path.
    ///
    /// This removes the bounded `other_node_snapshot_nodes` seam for callers
    /// that have the live process graph available. The lower-level bounded
    /// helpers stay available for unit-level coverage and partial integrations.
    pub fn analyse_satisfiable_task_classification_messages_with_live_other_nodes<
        O: ClassificationMessageDataObserver,
    >(
        &self,
        adapter: &SatisfiableTaskClassificationMessageAdapter,
        process_context: &ProcessContext,
        ontology: &OntologyArenas,
        constructed_individual_node: NodeId,
        individual_node_vector: &IndividualProcessNodeVector,
        max_deterministic_branch_tag: Cint64,
        equivalent_non_candidate_concepts: &std::collections::HashMap<ConceptId, Vec<ConceptId>>,
        concepts: &Arena<Concept>,
        concept_process_datas: &Arena<ConceptProcessData>,
        concept_reference_linking_datas: &Arena<ConceptSaturationReferenceLinkingData>,
        testing_items: &[OptimizedKPSetClassTestingItem],
        roles: &Arena<Role>,
        memory_pool: Cint64,
        observer: Option<&mut O>,
    ) -> Option<ClassificationAnalyserBoundedIntegrationResult> {
        let corrected_individual = self.get_corrected_individual_id(
            process_context,
            constructed_individual_node,
            individual_node_vector,
        )?;
        let (root_successor_individual_ids, other_node_snapshots) = self
            .collect_live_other_node_snapshots_from_root(
                process_context,
                ontology,
                corrected_individual.node,
            );

        let possible_subsumption_states = self
            .collect_possible_subsumption_states_from_classifier_references_for_snapshots(
                adapter,
                process_context,
                corrected_individual,
                &root_successor_individual_ids,
                &other_node_snapshots,
                concepts,
                concept_process_datas,
                concept_reference_linking_datas,
                testing_items,
            );

        let concepts_requiring_more_information = {
            let visits = self.collect_other_node_analyse_visits(
                adapter,
                corrected_individual.individual_id,
                &root_successor_individual_ids,
                &other_node_snapshots,
            );
            self.collect_other_node_concepts_requiring_more_information(
                adapter,
                &visits,
                concepts,
                concept_process_datas,
                concept_reference_linking_datas,
                testing_items,
            )
        };

        self.analyse_satisfiable_task_classification_messages_from_prebuilt_other_node_snapshots(
            adapter,
            process_context,
            ontology,
            constructed_individual_node,
            individual_node_vector,
            max_deterministic_branch_tag,
            &possible_subsumption_states,
            equivalent_non_candidate_concepts,
            &concepts_requiring_more_information,
            &root_successor_individual_ids,
            &other_node_snapshots,
            concepts,
            roles,
            memory_pool,
            observer,
        )
    }

    pub fn analyse_satisfiable_task_classification_messages_with_live_other_nodes_and_live_equivalent_non_candidates<
        O: ClassificationMessageDataObserver,
    >(
        &self,
        adapter: &SatisfiableTaskClassificationMessageAdapter,
        process_context: &mut ProcessContext,
        ontology: &OntologyArenas,
        constructed_individual_node: NodeId,
        individual_node_vector: &IndividualProcessNodeVector,
        max_deterministic_branch_tag: Cint64,
        concepts: &Arena<Concept>,
        concept_process_datas: &Arena<ConceptProcessData>,
        concept_reference_linking_datas: &Arena<ConceptSaturationReferenceLinkingData>,
        saturation_concept_reference_linkings: &Arena<SaturationConceptReferenceLinking>,
        testing_items: &[OptimizedKPSetClassTestingItem],
        roles: &Arena<Role>,
        has_value_space_triggers: bool,
        memory_pool: Cint64,
        observer: Option<&mut O>,
    ) -> Option<ClassificationAnalyserBoundedIntegrationResult> {
        let corrected_individual = self.get_corrected_individual_id(
            process_context,
            constructed_individual_node,
            individual_node_vector,
        )?;
        let (root_successor_individual_ids, other_node_snapshots) = self
            .collect_live_other_node_snapshots_from_root(
                process_context,
                ontology,
                corrected_individual.node,
            );

        let possible_subsumption_states = self
            .collect_possible_subsumption_states_from_classifier_references_for_snapshots(
                adapter,
                process_context,
                corrected_individual,
                &root_successor_individual_ids,
                &other_node_snapshots,
                concepts,
                concept_process_datas,
                concept_reference_linking_datas,
                testing_items,
            );

        let concepts_requiring_more_information = {
            let visits = self.collect_other_node_analyse_visits(
                adapter,
                corrected_individual.individual_id,
                &root_successor_individual_ids,
                &other_node_snapshots,
            );
            self.collect_other_node_concepts_requiring_more_information(
                adapter,
                &visits,
                concepts,
                concept_process_datas,
                concept_reference_linking_datas,
                testing_items,
            )
        };

        let root_result = self
            .create_root_classification_message_linkers_from_constructed_node_with_live_equivalent_non_candidates(
                adapter,
                process_context,
                ontology,
                constructed_individual_node,
                individual_node_vector,
                max_deterministic_branch_tag,
                &possible_subsumption_states,
                concepts,
                roles,
                concept_process_datas,
                concept_reference_linking_datas,
                saturation_concept_reference_linkings,
                None,
            )?;

        let visits = self.collect_other_node_analyse_visits(
            adapter,
            root_result.corrected_individual.individual_id,
            &root_successor_individual_ids,
            &other_node_snapshots,
        );
        let mut analysed_concepts = std::collections::HashSet::new();
        let (other_subsum_linker, other_poss_linker) = self
            .create_other_node_classification_message_linkers_with_live_equivalent_non_candidates(
                adapter,
                adapter.get_testing_concept(),
                &visits,
                &other_node_snapshots,
                &concepts_requiring_more_information,
                &mut analysed_concepts,
                &possible_subsumption_states,
                process_context,
                ontology,
                individual_node_vector,
                concepts,
                roles,
                concept_process_datas,
                concept_reference_linking_datas,
                saturation_concept_reference_linkings,
                None,
            );

        let subsum_message_data_linker =
            match (other_subsum_linker, root_result.subsum_message_data_linker) {
                (Some(other), Some(root)) => Some(other.append_linker(root)),
                (Some(other), None) => Some(other),
                (None, Some(root)) => Some(root),
                (None, None) => None,
            };
        let poss_subsum_message_data_linker = match (
            other_poss_linker,
            root_result.poss_subsum_message_data_linker,
        ) {
            (Some(other), Some(root)) => Some(other.append_linker(root)),
            (Some(other), None) => Some(other),
            (None, Some(root)) => Some(root),
            (None, None) => None,
        };

        let pm_message_data_linker = (!has_value_space_triggers)
            .then(|| {
                self.create_pseudo_model_identifier_message_linker_from_base_node(
                    adapter,
                    process_context,
                    root_result.corrected_individual.node,
                    root_result.corrected_individual.nondeterministically_merged,
                    root_result.max_deterministic_branch_tag,
                    concepts,
                    roles,
                    memory_pool,
                )
            })
            .flatten();

        let output = self.deliver_merged_classification_message_data(
            adapter,
            subsum_message_data_linker,
            pm_message_data_linker,
            poss_subsum_message_data_linker,
            memory_pool,
            observer,
        );

        Some(ClassificationAnalyserBoundedIntegrationResult {
            corrected_individual: root_result.corrected_individual,
            max_deterministic_branch_tag: root_result.max_deterministic_branch_tag,
            other_node_visit_count: visits.len(),
            output,
        })
    }

    /// Task/context-facing port of the opening and final delegation shape of
    /// `CSatisfiableTaskClassificationMessageAnalyser::analyseSatisfiableTask`.
    ///
    /// The body reads `statCalcTask->getClassificationMessageAdapter()`,
    /// `statCalcTask->getProcessingDataBox()`, and the static terminology from
    /// `calcAlgContext`, then delegates to the live W270 analyser path. The
    /// remaining scheduler/event allocation details stay outside this wrapper.
    pub fn analyse_satisfiable_task_from_context<O: ClassificationMessageDataObserver>(
        &self,
        sat_calc_task: Id<SatisfiableCalculationTask>,
        calc_alg_context: &mut CalculationAlgorithmContext,
        testing_items: &[OptimizedKPSetClassTestingItem],
        memory_pool: Cint64,
        observer: Option<&mut O>,
    ) -> Option<ClassificationAnalyserBoundedIntegrationResult> {
        let (adapter_id, constructed_individual_node, individual_node_vector, max_branch_tag) = {
            let task = calc_alg_context.try_sat_calc_task(sat_calc_task)?;
            let adapter_id = task.get_classification_message_adapter();
            if adapter_id.is_none()
                || adapter_id.index() >= calc_alg_context.classification_message_adapter_arena.len()
            {
                return None;
            }
            let data_box = task.processing_data_box_state()?;
            (
                adapter_id,
                data_box.constructed_individual_node(),
                data_box.individual_process_node_vector().clone(),
                data_box.maximum_deterministic_branch_tag(),
            )
        };

        let adapter = calc_alg_context
            .classification_message_adapter(adapter_id)
            .clone();
        let has_value_space_triggers = calc_alg_context.ontology_arenas.has_value_spaces_triggers();
        self.analyse_satisfiable_task_classification_messages_with_live_other_nodes_and_live_equivalent_non_candidates(
            &adapter,
            &mut calc_alg_context.used_process_context,
            &calc_alg_context.ontology_arenas,
            constructed_individual_node,
            &individual_node_vector,
            max_branch_tag,
            calc_alg_context.ontology_arenas.concepts(),
            calc_alg_context.ontology_arenas.concept_process_datas(),
            calc_alg_context
                .ontology_arenas
                .concept_saturation_reference_linking_datas(),
            calc_alg_context
                .ontology_arenas
                .saturation_concept_reference_linkings(),
            testing_items,
            calc_alg_context.ontology_arenas.roles(),
            has_value_space_triggers,
            memory_pool,
            observer,
        )
    }

    /// Registry-backed task/context entry.
    ///
    /// This mirrors the C++ ownership shape more closely than the test-facing
    /// generic overload above: the task's classification adapter owns the
    /// `CClassificationMessageDataObserver*` pointer, and the analyser resolves
    /// that handle through the classifier-thread observer registry before
    /// delivering the final message chain.
    pub fn analyse_satisfiable_task_from_context_with_registered_observer<
        O: ClassificationMessageDataObserver,
    >(
        &self,
        sat_calc_task: Id<SatisfiableCalculationTask>,
        calc_alg_context: &mut CalculationAlgorithmContext,
        testing_items: &[OptimizedKPSetClassTestingItem],
        memory_pool: Cint64,
        observer_registry: Option<&mut ClassificationMessageDataObserverRegistry<O>>,
    ) -> Option<ClassificationAnalyserBoundedIntegrationResult> {
        let observer_handle = {
            let task = calc_alg_context.try_sat_calc_task(sat_calc_task)?;
            let adapter_id = task.get_classification_message_adapter();
            if adapter_id.is_none()
                || adapter_id.index() >= calc_alg_context.classification_message_adapter_arena.len()
            {
                return None;
            }
            calc_alg_context
                .classification_message_adapter(adapter_id)
                .get_classification_message_data_observer()
        };
        let observer =
            observer_registry.and_then(|registry| registry.get_observer_mut(observer_handle));
        self.analyse_satisfiable_task_from_context(
            sat_calc_task,
            calc_alg_context,
            testing_items,
            memory_pool,
            observer,
        )
    }

    /// Collect possible-subsumption reference state for the root and bounded
    /// other-node analyser concepts.
    pub fn collect_possible_subsumption_states_from_classifier_references(
        &self,
        adapter: &SatisfiableTaskClassificationMessageAdapter,
        process_context: &ProcessContext,
        ontology: &OntologyArenas,
        constructed_individual_node: NodeId,
        individual_node_vector: &IndividualProcessNodeVector,
        other_node_snapshot_nodes: &[NodeId],
        concepts: &Arena<Concept>,
        concept_process_datas: &Arena<ConceptProcessData>,
        concept_reference_linking_datas: &Arena<ConceptSaturationReferenceLinkingData>,
        testing_items: &[OptimizedKPSetClassTestingItem],
    ) -> Option<std::collections::HashMap<ConceptId, ClassificationAnalyserPossibleSubsumptionState>>
    {
        let corrected_individual = self.get_corrected_individual_id(
            process_context,
            constructed_individual_node,
            individual_node_vector,
        )?;
        let mut states = std::collections::HashMap::new();

        let root_label_set = process_context
            .node(corrected_individual.node)
            .use_reapply_con_label_set;
        for label in self
            .extract_classification_analyser_labels_from_label_set(process_context, root_label_set)
        {
            if self.is_possible_subsumption_state_candidate(
                adapter.get_testing_concept(),
                label.concept,
                label.negated,
                concepts,
            ) {
                if let Some(state) = self
                    .possible_subsumption_state_for_concept_from_classifier_references(
                        label.concept,
                        concepts,
                        concept_process_datas,
                        concept_reference_linking_datas,
                        adapter,
                        testing_items,
                    )
                {
                    states.insert(label.concept, state);
                }
            }
        }

        let mut other_node_snapshots = Vec::new();
        for node in other_node_snapshot_nodes {
            if let Some(snapshot) = self
                .extract_other_node_snapshot_from_process_node_resolving_single_dependency(
                    process_context,
                    ontology,
                    *node,
                )
            {
                other_node_snapshots.push(snapshot);
            }
        }
        let mut root_successor_individual_ids = Vec::new();
        let mut succ_it = process_context.node_successor_iterator(corrected_individual.node);
        while succ_it.has_next() {
            let succ_indi_id = succ_it.next_individual_id(true);
            if succ_indi_id != 0 {
                root_successor_individual_ids.push(succ_indi_id);
            }
        }
        let visits = self.collect_other_node_analyse_visits(
            adapter,
            corrected_individual.individual_id,
            &root_successor_individual_ids,
            &other_node_snapshots,
        );
        for visit in visits {
            if self.is_possible_subsumption_state_candidate(
                adapter.get_testing_concept(),
                visit.label.concept,
                visit.label.negated,
                concepts,
            ) {
                if let Some(state) = self
                    .possible_subsumption_state_for_concept_from_classifier_references(
                        visit.label.concept,
                        concepts,
                        concept_process_datas,
                        concept_reference_linking_datas,
                        adapter,
                        testing_items,
                    )
                {
                    states.insert(visit.label.concept, state);
                }
            }
        }

        Some(states)
    }

    fn collect_possible_subsumption_states_from_classifier_references_for_snapshots(
        &self,
        adapter: &SatisfiableTaskClassificationMessageAdapter,
        process_context: &ProcessContext,
        corrected_individual: ClassificationAnalyserCorrectedIndividual,
        root_successor_individual_ids: &[Cint64],
        other_node_snapshots: &[ClassificationAnalyserOtherNodeSnapshot],
        concepts: &Arena<Concept>,
        concept_process_datas: &Arena<ConceptProcessData>,
        concept_reference_linking_datas: &Arena<ConceptSaturationReferenceLinkingData>,
        testing_items: &[OptimizedKPSetClassTestingItem],
    ) -> std::collections::HashMap<ConceptId, ClassificationAnalyserPossibleSubsumptionState> {
        let mut states = std::collections::HashMap::new();

        let root_label_set = process_context
            .node(corrected_individual.node)
            .use_reapply_con_label_set;
        for label in self
            .extract_classification_analyser_labels_from_label_set(process_context, root_label_set)
        {
            if self.is_possible_subsumption_state_candidate(
                adapter.get_testing_concept(),
                label.concept,
                label.negated,
                concepts,
            ) {
                if let Some(state) = self
                    .possible_subsumption_state_for_concept_from_classifier_references(
                        label.concept,
                        concepts,
                        concept_process_datas,
                        concept_reference_linking_datas,
                        adapter,
                        testing_items,
                    )
                {
                    states.insert(label.concept, state);
                }
            }
        }

        let visits = self.collect_other_node_analyse_visits(
            adapter,
            corrected_individual.individual_id,
            root_successor_individual_ids,
            other_node_snapshots,
        );
        for visit in visits {
            if self.is_possible_subsumption_state_candidate(
                adapter.get_testing_concept(),
                visit.label.concept,
                visit.label.negated,
                concepts,
            ) {
                if let Some(state) = self
                    .possible_subsumption_state_for_concept_from_classifier_references(
                        visit.label.concept,
                        concepts,
                        concept_process_datas,
                        concept_reference_linking_datas,
                        adapter,
                        testing_items,
                    )
                {
                    states.insert(visit.label.concept, state);
                }
            }
        }

        states
    }

    fn is_possible_subsumption_state_candidate(
        &self,
        testing_concept: ConceptId,
        concept: ConceptId,
        negated: bool,
        concepts: &Arena<Concept>,
    ) -> bool {
        !negated
            && concept != testing_concept
            && Self::is_named_class(concept, concepts)
            && Self::concept_tag(concept, concepts) != 1
    }

    /// Resolve the analyser-side possible-subsumption snapshot for one
    /// classifier-reference-backed concept.
    pub fn possible_subsumption_state_for_concept_from_classifier_references(
        &self,
        concept: ConceptId,
        concepts: &Arena<Concept>,
        concept_process_datas: &Arena<ConceptProcessData>,
        concept_reference_linking_datas: &Arena<ConceptSaturationReferenceLinkingData>,
        adapter: &SatisfiableTaskClassificationMessageAdapter,
        testing_items: &[OptimizedKPSetClassTestingItem],
    ) -> Option<ClassificationAnalyserPossibleSubsumptionState> {
        let class_ref_link_data = Self::classification_reference_linking_data_for_concept(
            concept,
            concepts,
            concept_process_datas,
            concept_reference_linking_datas,
            adapter,
        )?;
        let item_id = OptimizedKPSetClassTestingItemId::new(class_ref_link_data);
        if item_id.is_none() || item_id.index() >= testing_items.len() {
            return None;
        }
        let testing_item = &testing_items[item_id.index()];
        if !testing_item.is_possible_subsumption_map_initialized() {
            return Some(ClassificationAnalyserPossibleSubsumptionState::uninitialized());
        }

        let Some(possible_subsumption_map) = testing_item.get_possible_subsumption_map_ref() else {
            return Some(ClassificationAnalyserPossibleSubsumptionState {
                possible_subsumption_map_initialized: true,
                remaining_possible_subsumptions: false,
                possible_subsumption_concepts: Vec::new(),
            });
        };
        let mut possible_subsumption_concepts = possible_subsumption_map.concepts();
        possible_subsumption_concepts.sort_by_key(|concept| Self::concept_tag(*concept, concepts));
        Some(ClassificationAnalyserPossibleSubsumptionState {
            possible_subsumption_map_initialized: true,
            remaining_possible_subsumptions: possible_subsumption_map
                .has_remaining_possible_subsumptions(),
            possible_subsumption_concepts,
        })
    }

    fn classification_reference_linking_data_for_concept(
        concept: ConceptId,
        concepts: &Arena<Concept>,
        concept_process_datas: &Arena<ConceptProcessData>,
        concept_reference_linking_datas: &Arena<ConceptSaturationReferenceLinkingData>,
        adapter: &SatisfiableTaskClassificationMessageAdapter,
    ) -> Option<Cint64> {
        if concept.is_none() || concept.index() >= concepts.len() {
            return None;
        }
        let concept_data = concepts.get(concept);
        if concept_data.has_concept_data() {
            let con_proc_data_id = Id::<ConceptProcessData>::new(concept_data.get_concept_data());
            if con_proc_data_id.is_some() && con_proc_data_id.index() < concept_process_datas.len()
            {
                let con_proc_data = concept_process_datas.get(con_proc_data_id);
                if !con_proc_data.is_invalidated_reference_linking() {
                    let con_ref_linking_id = con_proc_data.get_concept_reference_linking();
                    if con_ref_linking_id.is_some()
                        && con_ref_linking_id.index() < concept_reference_linking_datas.len()
                    {
                        let raw = concept_reference_linking_datas
                            .get(con_ref_linking_id)
                            .get_classifier_reference_linking_data();
                        if raw != INVALID {
                            return Some(raw);
                        }
                    }
                }
            }
        }
        adapter
            .get_concept_reference_linking_data_hash()
            .get(&concept)
            .copied()
            .filter(|raw| *raw != INVALID)
    }

    /// Port of
    /// `CSatisfiableTaskClassificationMessageAnalyser::getSaturatedIndividualNodeForConcept`.
    pub fn get_saturated_individual_node_for_concept(
        &self,
        concept: ConceptId,
        concept_negation: bool,
        concepts: &Arena<Concept>,
        concept_process_datas: &Arena<ConceptProcessData>,
        concept_reference_linking_datas: &Arena<ConceptSaturationReferenceLinkingData>,
        saturation_concept_reference_linkings: &Arena<SaturationConceptReferenceLinking>,
        process_context: &ProcessContext,
    ) -> Option<SatNodeId> {
        if concept.is_none() || concept.index() >= concepts.len() {
            return None;
        }
        let concept_data = concepts.get(concept);
        if !concept_data.has_concept_data() {
            return None;
        }

        let con_proc_data_id = Id::<ConceptProcessData>::new(concept_data.get_concept_data());
        if con_proc_data_id.is_none() || con_proc_data_id.index() >= concept_process_datas.len() {
            return None;
        }
        let con_ref_linking_id = concept_process_datas
            .get(con_proc_data_id)
            .get_concept_reference_linking();
        if con_ref_linking_id.is_none()
            || con_ref_linking_id.index() >= concept_reference_linking_datas.len()
        {
            return None;
        }
        let sat_calc_ref_link_data_id = concept_reference_linking_datas
            .get(con_ref_linking_id)
            .get_concept_saturation_reference_linking_data(concept_negation);
        if sat_calc_ref_link_data_id.is_none()
            || sat_calc_ref_link_data_id.index() >= saturation_concept_reference_linkings.len()
        {
            return None;
        }
        let sat_node = saturation_concept_reference_linkings
            .get(sat_calc_ref_link_data_id)
            .get_individual_process_node_for_concept();
        if sat_node.is_none() || sat_node.index() >= process_context.sat_node_count() {
            return None;
        }
        Some(sat_node)
    }

    /// Port of
    /// `CSatisfiableTaskClassificationMessageAnalyser::getExistentialSaturatedIndividualNodeForConcept`.
    pub fn get_existential_saturated_individual_node_for_concept(
        &self,
        concept: ConceptId,
        concepts: &Arena<Concept>,
        concept_process_datas: &Arena<ConceptProcessData>,
        concept_reference_linking_datas: &Arena<ConceptSaturationReferenceLinkingData>,
        saturation_concept_reference_linkings: &Arena<SaturationConceptReferenceLinking>,
        process_context: &ProcessContext,
        ontology_top_concept: Option<ConceptId>,
    ) -> Option<SatNodeId> {
        if concept.is_none() || concept.index() >= concepts.len() {
            return None;
        }
        let concept_data = concepts.get(concept);
        if concept_data.has_concept_data() {
            let con_proc_data_id = Id::<ConceptProcessData>::new(concept_data.get_concept_data());
            if con_proc_data_id.is_some() && con_proc_data_id.index() < concept_process_datas.len()
            {
                let con_ref_linking_id = concept_process_datas
                    .get(con_proc_data_id)
                    .get_concept_reference_linking();
                if con_ref_linking_id.is_some()
                    && con_ref_linking_id.index() < concept_reference_linking_datas.len()
                {
                    let sat_calc_ref_link_data_id = concept_reference_linking_datas
                        .get(con_ref_linking_id)
                        .get_existential_successor_concept_saturation_reference_linking_data();
                    if sat_calc_ref_link_data_id.is_some()
                        && sat_calc_ref_link_data_id.index()
                            < saturation_concept_reference_linkings.len()
                    {
                        let sat_node = saturation_concept_reference_linkings
                            .get(sat_calc_ref_link_data_id)
                            .get_individual_process_node_for_concept();
                        if sat_node.is_some() && sat_node.index() < process_context.sat_node_count()
                        {
                            return Some(sat_node);
                        }
                    }
                }
            }
        }

        let operands = concept_data.get_operand_list();
        let mut op_concept = ConceptId::NONE;
        let mut op_negation = false;
        if operands.is_empty() {
            op_concept = ontology_top_concept.unwrap_or(ConceptId::NONE);
        } else if operands.len() == 1 {
            let op_linker = &operands[0];
            op_concept = op_linker.target;
            let negate_op = concept_data.get_operator_code() == CCALL;
            op_negation = op_linker.negated ^ negate_op;
        }

        if op_concept.is_some() {
            return self.get_saturated_individual_node_for_concept(
                op_concept,
                op_negation,
                concepts,
                concept_process_datas,
                concept_reference_linking_datas,
                saturation_concept_reference_linkings,
                process_context,
            );
        }
        None
    }

    /// Port of
    /// `CSatisfiableTaskClassificationMessageAnalyser::collectTrivialPropagationTestingConcepts`.
    pub fn collect_trivial_propagation_testing_concepts(
        &self,
        concept: ConceptId,
        negation: bool,
        concepts: &Arena<Concept>,
        trivial_concept_testing_list: &mut Vec<(ConceptId, bool)>,
    ) -> bool {
        if concept.is_none() || concept.index() >= concepts.len() {
            return false;
        }
        let concept_ref = concepts.get(concept);
        let con_op_code = concept_ref.get_operator_code();
        if negation && con_op_code == CCSUB {
            trivial_concept_testing_list.push((concept, negation));
            return true;
        } else if !negation
            && (con_op_code == CCALL
                || con_op_code == CCIMPLALL
                || con_op_code == CCBRANCHALL
                || con_op_code == CCAQALL
                || con_op_code == CCIMPLAQALL
                || con_op_code == CCBRANCHAQALL)
        {
            trivial_concept_testing_list.push((concept, negation));
            return true;
        } else if !negation
            && (con_op_code == CCAQAND
                || con_op_code == CCIMPLAQAND
                || con_op_code == CCBRANCHAQAND)
        {
            let mut all_operands_succeeded = true;
            for operand in concept_ref.get_operand_list() {
                all_operands_succeeded &= self.collect_trivial_propagation_testing_concepts(
                    operand.target,
                    operand.negated,
                    concepts,
                    trivial_concept_testing_list,
                );
            }
            return all_operands_succeeded;
        }
        false
    }

    /// Port of
    /// `CSatisfiableTaskClassificationMessageAnalyser::addAutomateTransactionConcepts`.
    pub fn add_automate_transaction_concepts(
        &self,
        concept: ConceptId,
        negation: bool,
        role: RoleId,
        concepts: &Arena<Concept>,
        concept_process_datas: &Arena<ConceptProcessData>,
        concept_reference_linking_datas: &Arena<ConceptSaturationReferenceLinkingData>,
        saturation_concept_reference_linkings: &Arena<SaturationConceptReferenceLinking>,
        process_context: &ProcessContext,
        successor_list: &mut Vec<SatNodeId>,
        trivial_concept_testing_list: &mut Vec<(ConceptId, bool)>,
    ) -> bool {
        if concept.is_none() || concept.index() >= concepts.len() {
            return false;
        }
        let concept_ref = concepts.get(concept);
        let con_op_code = concept_ref.get_operator_code();
        if !negation
            && (con_op_code == CCAQALL
                || con_op_code == CCIMPLAQALL
                || con_op_code == CCBRANCHAQALL)
        {
            if concept_ref.get_role() == role {
                for operand in concept_ref.get_operand_list() {
                    let reapply_operand_con = operand.target;
                    let reapply_operand_con_neg = operand.negated;
                    let sat_indi_node = self.get_saturated_individual_node_for_concept(
                        reapply_operand_con,
                        reapply_operand_con_neg,
                        concepts,
                        concept_process_datas,
                        concept_reference_linking_datas,
                        saturation_concept_reference_linkings,
                        process_context,
                    );
                    if let Some(sat_indi_node) = sat_indi_node {
                        if !Self::is_saturated_successor_merge_dependency_eligible(
                            process_context,
                            sat_indi_node,
                        ) {
                            return false;
                        }
                        successor_list.push(sat_indi_node);
                    } else if !self.collect_trivial_propagation_testing_concepts(
                        reapply_operand_con,
                        reapply_operand_con_neg,
                        concepts,
                        trivial_concept_testing_list,
                    ) {
                        return false;
                    }
                }
            }
        } else if !negation
            && (con_op_code == CCAQAND
                || con_op_code == CCIMPLAQAND
                || con_op_code == CCBRANCHAQAND)
        {
            let mut all_operands_succeeded = true;
            for operand in concept_ref.get_operand_list() {
                all_operands_succeeded &= self.add_automate_transaction_concepts(
                    operand.target,
                    operand.negated,
                    role,
                    concepts,
                    concept_process_datas,
                    concept_reference_linking_datas,
                    saturation_concept_reference_linkings,
                    process_context,
                    successor_list,
                    trivial_concept_testing_list,
                );
            }
            return all_operands_succeeded;
        }
        true
    }

    fn collect_successor_merging_operand(
        &self,
        concept: ConceptId,
        negation: bool,
        concepts: &Arena<Concept>,
        concept_process_datas: &Arena<ConceptProcessData>,
        concept_reference_linking_datas: &Arena<ConceptSaturationReferenceLinkingData>,
        saturation_concept_reference_linkings: &Arena<SaturationConceptReferenceLinking>,
        process_context: &ProcessContext,
        successor_list: &mut Vec<SatNodeId>,
        trivial_successor_propagated_concept_list: &mut Vec<(ConceptId, bool)>,
    ) -> bool {
        let sat_indi_node = self.get_saturated_individual_node_for_concept(
            concept,
            negation,
            concepts,
            concept_process_datas,
            concept_reference_linking_datas,
            saturation_concept_reference_linkings,
            process_context,
        );
        if let Some(sat_indi_node) = sat_indi_node {
            if !Self::is_saturated_successor_merge_dependency_eligible(
                process_context,
                sat_indi_node,
            ) {
                return false;
            }
            successor_list.push(sat_indi_node);
            true
        } else {
            self.collect_trivial_propagation_testing_concepts(
                concept,
                negation,
                concepts,
                trivial_successor_propagated_concept_list,
            )
        }
    }

    /// Port of the completion-node overload of
    /// `CSatisfiableTaskClassificationMessageAnalyser::collectSuccessorMergingNodesAndConcepts`.
    pub fn collect_successor_merging_nodes_and_concepts_for_completion_node(
        &self,
        indi_node: NodeId,
        role: RoleId,
        concepts: &Arena<Concept>,
        roles: &Arena<Role>,
        concept_process_datas: &Arena<ConceptProcessData>,
        concept_reference_linking_datas: &Arena<ConceptSaturationReferenceLinkingData>,
        saturation_concept_reference_linkings: &Arena<SaturationConceptReferenceLinking>,
        process_context: &mut ProcessContext,
        successor_list: &mut Vec<SatNodeId>,
        trivial_successor_propagated_concept_list: &mut Vec<(ConceptId, bool)>,
        backward_role_set: &mut std::collections::HashSet<RoleId>,
    ) -> bool {
        if role.is_none() || role.index() >= roles.len() {
            return false;
        }
        let role_succ_hash =
            if indi_node.is_none() || indi_node.index() >= process_context.node_count() {
                super::super::process::RoleSuccHashId::NONE
            } else {
                process_context.node_reapply_role_successor_hash_existing(indi_node)
            };

        for super_role_link in roles.get(role).get_indirect_super_role_list() {
            let super_role = super_role_link.target;
            let super_role_inversed = super_role_link.negated;
            if role_succ_hash.is_some() && !super_role_inversed {
                let mut reapply_it = process_context
                    .role_succ_hash_mut(role_succ_hash)
                    .get_role_reapply_iterator(super_role, false);
                while reapply_it.has_next() {
                    let reapply_con_des = reapply_it.next(process_context, true);
                    if reapply_con_des.is_none() {
                        return false;
                    }
                    let con_des = process_context
                        .reapply_con_desc(reapply_con_des)
                        .get_concept_descriptor();
                    if con_des.is_none() {
                        return false;
                    }
                    let con_des_ref = process_context.con_desc(con_des);
                    let reapply_concept = con_des_ref.concept;
                    if reapply_concept.is_none() || reapply_concept.index() >= concepts.len() {
                        return false;
                    }
                    let reapply_concept_negation = con_des_ref.negated;
                    let reapply_concept_ref = concepts.get(reapply_concept);
                    let reapply_concept_op_code = reapply_concept_ref.get_operator_code();
                    if (reapply_concept_negation && reapply_concept_op_code == CCSOME)
                        || (!reapply_concept_negation
                            && (reapply_concept_op_code == CCALL
                                || reapply_concept_op_code == CCIMPLALL
                                || reapply_concept_op_code == CCBRANCHALL
                                || reapply_concept_op_code == CCAQALL
                                || reapply_concept_op_code == CCIMPLAQALL
                                || reapply_concept_op_code == CCBRANCHAQALL))
                    {
                        for operand in reapply_concept_ref.get_operand_list() {
                            if !self.collect_successor_merging_operand(
                                operand.target,
                                operand.negated ^ reapply_concept_negation,
                                concepts,
                                concept_process_datas,
                                concept_reference_linking_datas,
                                saturation_concept_reference_linkings,
                                process_context,
                                successor_list,
                                trivial_successor_propagated_concept_list,
                            ) {
                                return false;
                            }
                        }
                    } else if !reapply_concept_negation
                        && (reapply_concept_op_code == CCAQAND
                            || reapply_concept_op_code == CCIMPLAQAND
                            || reapply_concept_op_code == CCBRANCHAQAND)
                    {
                        if !self.add_automate_transaction_concepts(
                            reapply_concept,
                            reapply_concept_negation,
                            super_role,
                            concepts,
                            concept_process_datas,
                            concept_reference_linking_datas,
                            saturation_concept_reference_linkings,
                            process_context,
                            successor_list,
                            trivial_successor_propagated_concept_list,
                        ) {
                            return false;
                        }
                    } else {
                        return false;
                    }
                }
            } else {
                backward_role_set.insert(super_role);
            }
        }

        true
    }

    /// Port of the recursive saturation-node overload of
    /// `CSatisfiableTaskClassificationMessageAnalyser::collectSuccessorMergingNodesAndConcepts`.
    ///
    /// `successor_influence_concepts` is the port-side representation of the
    /// C++ `CPROCESSINGHASH<CRole*,TConceptNegationPair>` iteration window: it is
    /// scanned from the first `superRole` entry and then stopped at the first
    /// non-matching key, preserving the upstream `constFind(...)`/`break` shape.
    pub fn collect_successor_merging_nodes_and_concepts_for_saturation_node(
        &self,
        exclude_saturation_indi_node: SatNodeId,
        role: RoleId,
        concepts: &Arena<Concept>,
        roles: &Arena<Role>,
        concept_process_datas: &Arena<ConceptProcessData>,
        concept_reference_linking_datas: &Arena<ConceptSaturationReferenceLinkingData>,
        saturation_concept_reference_linkings: &Arena<SaturationConceptReferenceLinking>,
        process_context: &ProcessContext,
        successor_list: &[SatNodeId],
        next_successor_list: &mut Vec<SatNodeId>,
        next_trivial_successor_propagated_concept_list: &mut Vec<(ConceptId, bool)>,
        next_backward_role_set: &mut std::collections::HashSet<RoleId>,
        successor_influence_concepts: &[(RoleId, (ConceptId, bool))],
    ) -> bool {
        if role.is_none() || role.index() >= roles.len() {
            return false;
        }

        for super_role_link in roles.get(role).get_indirect_super_role_list() {
            let super_role = super_role_link.target;
            let super_role_inversed = super_role_link.negated;

            if !super_role_inversed {
                if let Some(start_index) = successor_influence_concepts
                    .iter()
                    .position(|(hash_role, _)| *hash_role == super_role)
                {
                    for (hash_role, (reapply_operand_con, reapply_operand_con_neg)) in
                        successor_influence_concepts[start_index..].iter()
                    {
                        if *hash_role == role {
                            if !self.collect_successor_merging_operand(
                                *reapply_operand_con,
                                *reapply_operand_con_neg,
                                concepts,
                                concept_process_datas,
                                concept_reference_linking_datas,
                                saturation_concept_reference_linkings,
                                process_context,
                                next_successor_list,
                                next_trivial_successor_propagated_concept_list,
                            ) {
                                return false;
                            }
                        } else {
                            break;
                        }
                    }
                }

                for succ_indi_node in successor_list.iter().copied() {
                    let mut succ_indi_node = succ_indi_node;
                    while succ_indi_node.is_some()
                        && succ_indi_node.index() < process_context.sat_node_count()
                        && process_context
                            .sat_node(succ_indi_node)
                            .has_substitute_individual_node()
                    {
                        succ_indi_node = process_context
                            .sat_node(succ_indi_node)
                            .get_substitute_individual_node();
                    }
                    if succ_indi_node.is_none()
                        || succ_indi_node.index() >= process_context.sat_node_count()
                    {
                        return false;
                    }

                    if succ_indi_node != exclude_saturation_indi_node {
                        let role_back_prop_hash =
                            process_context.sat_node(succ_indi_node).role_back_prop_hash;
                        if role_back_prop_hash.is_some() {
                            let reapply_linker = process_context
                                .role_backward_sat_prop_hash(role_back_prop_hash)
                                .get_backward_propagation_backward_propagation_concept_descriptor(
                                    super_role,
                                );
                            let mut reapply_linker_it = reapply_linker;
                            while reapply_linker_it.is_some() {
                                let reapply_con_des = process_context
                                    .backward_sat_prop_reapply_desc(reapply_linker_it)
                                    .get_reapply_concept_saturation_descriptor();
                                if reapply_con_des.is_none() {
                                    return false;
                                }
                                let reapply_con_des_ref =
                                    process_context.con_sat_desc(reapply_con_des);
                                let reapply_concept = reapply_con_des_ref.get_concept();
                                if reapply_concept.is_none()
                                    || reapply_concept.index() >= concepts.len()
                                {
                                    return false;
                                }
                                let reapply_concept_negation = reapply_con_des_ref.get_negation();
                                let reapply_concept_ref = concepts.get(reapply_concept);
                                let reapply_concept_op_code =
                                    reapply_concept_ref.get_operator_code();
                                if (reapply_concept_negation && reapply_concept_op_code == CCSOME)
                                    || (!reapply_concept_negation
                                        && (reapply_concept_op_code == CCALL
                                            || reapply_concept_op_code == CCIMPLALL
                                            || reapply_concept_op_code == CCBRANCHALL
                                            || reapply_concept_op_code == CCAQALL
                                            || reapply_concept_op_code == CCIMPLAQALL
                                            || reapply_concept_op_code == CCBRANCHAQALL))
                                {
                                    for operand in reapply_concept_ref.get_operand_list() {
                                        let operand_con = operand.target;
                                        let operand_neg =
                                            operand.negated ^ reapply_concept_negation;
                                        let sat_indi_node = self
                                            .get_saturated_individual_node_for_concept(
                                                operand_con,
                                                operand_neg,
                                                concepts,
                                                concept_process_datas,
                                                concept_reference_linking_datas,
                                                saturation_concept_reference_linkings,
                                                process_context,
                                            );
                                        if let Some(sat_indi_node) = sat_indi_node {
                                            if !Self::is_saturated_successor_merge_dependency_eligible(
                                                process_context,
                                                sat_indi_node,
                                            ) {
                                                return false;
                                            }
                                            next_successor_list.push(sat_indi_node);
                                        } else {
                                            if !self.collect_trivial_propagation_testing_concepts(
                                                operand_con,
                                                operand_neg,
                                                concepts,
                                                next_trivial_successor_propagated_concept_list,
                                            ) {
                                                return false;
                                            }
                                            next_successor_list.push(SatNodeId::NONE);
                                        }
                                    }
                                } else {
                                    return false;
                                }

                                reapply_linker_it = process_context
                                    .backward_sat_prop_reapply_desc(reapply_linker_it)
                                    .get_next();
                            }
                        }
                    }
                }
            } else {
                next_backward_role_set.insert(super_role);
            }
        }

        true
    }

    /// Port of the opening backward-role/trivial-propagation preparation block
    /// in `testMultipleSaturatedSuccessorModelMergable(...)`.
    pub fn prepare_multiple_saturated_successor_merge_triggers(
        &self,
        existential_indi_node: SatNodeId,
        successor_list: &[SatNodeId],
        trivial_successor_propagated_concept_list: &[(ConceptId, bool)],
        backward_role_set: &std::collections::HashSet<RoleId>,
        concepts: &Arena<Concept>,
        process_context: &ProcessContext,
    ) -> Option<(
        std::collections::HashMap<Cint64, ConceptNegationTriggerItem>,
        Vec<(RoleId, (ConceptId, bool))>,
    )> {
        for succ_indi_node in successor_list.iter().copied() {
            if succ_indi_node != existential_indi_node {
                let mut resolved_succ = succ_indi_node;
                while resolved_succ.is_some()
                    && resolved_succ.index() < process_context.sat_node_count()
                    && process_context
                        .sat_node(resolved_succ)
                        .has_substitute_individual_node()
                {
                    resolved_succ = process_context
                        .sat_node(resolved_succ)
                        .get_substitute_individual_node();
                }
                if resolved_succ.is_none()
                    || resolved_succ.index() >= process_context.sat_node_count()
                {
                    return None;
                }
                let role_backward_prop_hash =
                    process_context.sat_node(resolved_succ).role_back_prop_hash;
                if role_backward_prop_hash.is_some() {
                    let role_backward_prop_data_hash = process_context
                        .role_backward_sat_prop_hash(role_backward_prop_hash)
                        .get_role_backward_propagation_data_hash();
                    for backward_role in backward_role_set.iter().copied() {
                        if role_backward_prop_data_hash
                            .get(&backward_role)
                            .is_some_and(|data| data.link_linker.is_some())
                        {
                            return None;
                        }
                    }
                }
            }
        }

        let mut concept_negation_trigger_hash =
            std::collections::HashMap::<Cint64, ConceptNegationTriggerItem>::new();
        let mut successor_influence_concepts = Vec::new();
        for (concept, negation) in trivial_successor_propagated_concept_list.iter().copied() {
            if concept.is_none() || concept.index() >= concepts.len() {
                return None;
            }
            let concept_ref = concepts.get(concept);
            let con_op_code = concept_ref.get_operator_code();
            if negation && con_op_code == CCSUB {
                let con_tag = concept_ref.get_concept_tag();
                let con_neg_trigger_item =
                    concept_negation_trigger_hash.entry(con_tag).or_default();
                if con_neg_trigger_item.trigger_flag {
                    return None;
                }
                if con_neg_trigger_item.concept.is_some()
                    && con_neg_trigger_item.negation_flag != negation
                {
                    return None;
                }
                con_neg_trigger_item.negation_flag = negation;
                con_neg_trigger_item.concept = concept;
            } else if !negation
                && (con_op_code == CCALL
                    || con_op_code == CCIMPLALL
                    || con_op_code == CCBRANCHALL
                    || con_op_code == CCAQALL
                    || con_op_code == CCIMPLAQALL
                    || con_op_code == CCBRANCHAQALL)
            {
                let role = concept_ref.get_role();
                if backward_role_set.contains(&role) {
                    return None;
                }
                for operand in concept_ref.get_operand_list() {
                    successor_influence_concepts
                        .push((role, (operand.target, operand.negated ^ negation)));
                }
            }
        }

        Some((concept_negation_trigger_hash, successor_influence_concepts))
    }

    /// Port of the saturation label-set scan inside
    /// `testMultipleSaturatedSuccessorModelMergable(...)`.
    pub fn merge_successor_saturation_label_triggers(
        &self,
        successor_list: &[SatNodeId],
        concepts: &Arena<Concept>,
        process_context: &ProcessContext,
        concept_negation_trigger_hash: &mut std::collections::HashMap<
            Cint64,
            ConceptNegationTriggerItem,
        >,
    ) -> bool {
        for succ_indi_node in successor_list.iter().copied() {
            let mut succ_indi_node = succ_indi_node;
            while succ_indi_node.is_some()
                && succ_indi_node.index() < process_context.sat_node_count()
                && process_context
                    .sat_node(succ_indi_node)
                    .has_substitute_individual_node()
            {
                let concept_sat_item = process_context
                    .sat_node(succ_indi_node)
                    .get_saturation_concept_reference_linking();
                if concept_sat_item.is_none()
                    || concept_sat_item.index()
                        >= process_context.extended_con_ref_linking_data_count()
                {
                    return false;
                }
                let concept_sat_item_ref =
                    process_context.extended_con_ref_linking_data(concept_sat_item);
                let sat_concept = concept_sat_item_ref.get_saturation_concept();
                if sat_concept.is_none() || sat_concept.index() >= concepts.len() {
                    return false;
                }
                let sat_negation = concept_sat_item_ref.get_saturation_negation();
                let con_tag = concepts.get(sat_concept).get_concept_tag();
                let con_neg_trigger_item =
                    concept_negation_trigger_hash.entry(con_tag).or_default();
                if con_neg_trigger_item.trigger_flag {
                    return false;
                }
                if con_neg_trigger_item.concept.is_some()
                    && con_neg_trigger_item.negation_flag != sat_negation
                {
                    return false;
                }
                if con_neg_trigger_item.indi_sat_node.is_none() {
                    con_neg_trigger_item.indi_sat_node = succ_indi_node;
                }
                con_neg_trigger_item.negation_flag = sat_negation;
                con_neg_trigger_item.concept = sat_concept;
                succ_indi_node = process_context
                    .sat_node(succ_indi_node)
                    .get_substitute_individual_node();
            }
            if succ_indi_node.is_none()
                || succ_indi_node.index() >= process_context.sat_node_count()
            {
                return false;
            }

            let sat_con_set = process_context
                .sat_node(succ_indi_node)
                .reapply_con_sat_label_set;
            if sat_con_set.is_some()
                && sat_con_set.index() < process_context.reapply_con_sat_label_set_count()
            {
                let mut sat_con_set_it = process_context
                    .reapply_con_sat_label_set(sat_con_set)
                    .get_iterator(true, true);
                while sat_con_set_it.has_next() {
                    let data_tag = sat_con_set_it.get_data_tag();
                    let con_sat_des = sat_con_set_it.get_concept_saturation_descriptor();
                    let impl_trigger =
                        sat_con_set_it.get_implication_reapply_concept_saturation_descriptor();
                    let con_neg_trigger_item =
                        concept_negation_trigger_hash.entry(data_tag).or_default();
                    if con_sat_des.is_some() {
                        let con_sat_des_ref = process_context.con_sat_desc(con_sat_des);
                        let sat_concept = con_sat_des_ref.get_concept();
                        let sat_negation = con_sat_des_ref.get_negation();
                        if con_neg_trigger_item.trigger_flag {
                            return false;
                        }
                        if con_neg_trigger_item.concept.is_some()
                            && con_neg_trigger_item.negation_flag != sat_negation
                        {
                            return false;
                        }
                        if con_neg_trigger_item.indi_sat_node.is_none() {
                            con_neg_trigger_item.indi_sat_node = succ_indi_node;
                        }
                        con_neg_trigger_item.negation_flag = sat_negation;
                        con_neg_trigger_item.concept = sat_concept;
                    } else if impl_trigger.is_some() {
                        if con_neg_trigger_item.concept.is_some() {
                            return false;
                        }
                        con_neg_trigger_item.trigger_flag = true;
                    }
                    sat_con_set_it.move_next();
                }
            }
        }

        true
    }

    /// Port of the concept-trigger recursive-call preparation loop in
    /// `testMultipleSaturatedSuccessorModelMergable(...)`.
    ///
    /// The upstream block immediately calls
    /// `testSaturatedSuccessorModelMergable(...)` for each non-empty recursive
    /// successor/trivial set. That dispatcher is still a later exact-port slice,
    /// so this helper returns the prepared call payloads with the existential
    /// saturated node already prepended exactly as the C++ code does.
    pub fn collect_multiple_successor_recursive_merge_jobs_from_triggers(
        &self,
        concept_negation_trigger_hash: &std::collections::HashMap<
            Cint64,
            ConceptNegationTriggerItem,
        >,
        successor_list: &[SatNodeId],
        trivial_successor_propagated_concept_list: &[(ConceptId, bool)],
        backward_role_set: &std::collections::HashSet<RoleId>,
        successor_influence_concepts: &[(RoleId, (ConceptId, bool))],
        concepts: &Arena<Concept>,
        roles: &Arena<Role>,
        concept_process_datas: &Arena<ConceptProcessData>,
        concept_reference_linking_datas: &Arena<ConceptSaturationReferenceLinkingData>,
        saturation_concept_reference_linkings: &Arena<SaturationConceptReferenceLinking>,
        process_context: &ProcessContext,
        ontology_top_concept: Option<ConceptId>,
        jobs: &mut Vec<SaturatedSuccessorMergeJob>,
    ) -> bool {
        for con_neg_trigger_item in concept_negation_trigger_hash.values().copied() {
            if con_neg_trigger_item.concept.is_none() {
                continue;
            }
            let concept = con_neg_trigger_item.concept;
            if concept.index() >= concepts.len() {
                return false;
            }
            let concept_ref = concepts.get(concept);
            let negated = con_neg_trigger_item.negation_flag;
            let sat_indi_node = con_neg_trigger_item.indi_sat_node;
            let op_code = concept_ref.get_operator_code();
            let card = concept_ref.get_parameter();

            if (!negated
                && (op_code == CCSOME || op_code == CCAQSOME || (op_code == CCATLEAST && card > 0)))
                || (negated && (op_code == CCALL || (op_code == CCATMOST && card >= 0)))
            {
                let role = concept_ref.get_role();
                let mut next_successor_list = Vec::new();
                let mut next_trivial_successor_propagated_concept_list = Vec::new();
                let mut next_backward_role_set = std::collections::HashSet::new();

                if !self.collect_successor_merging_nodes_and_concepts_for_saturation_node(
                    sat_indi_node,
                    role,
                    concepts,
                    roles,
                    concept_process_datas,
                    concept_reference_linking_datas,
                    saturation_concept_reference_linkings,
                    process_context,
                    successor_list,
                    &mut next_successor_list,
                    &mut next_trivial_successor_propagated_concept_list,
                    &mut next_backward_role_set,
                    successor_influence_concepts,
                ) {
                    return false;
                }

                if !next_successor_list.is_empty()
                    || !trivial_successor_propagated_concept_list.is_empty()
                {
                    let ext_sat_indi_node = self
                        .get_existential_saturated_individual_node_for_concept(
                            concept,
                            concepts,
                            concept_process_datas,
                            concept_reference_linking_datas,
                            saturation_concept_reference_linkings,
                            process_context,
                            ontology_top_concept,
                        );
                    let Some(ext_sat_indi_node) = ext_sat_indi_node else {
                        return false;
                    };
                    next_successor_list.insert(0, ext_sat_indi_node);
                    jobs.push(SaturatedSuccessorMergeJob {
                        existential_sat_node: ext_sat_indi_node,
                        successor_list: next_successor_list,
                        trivial_successor_propagated_concept_list:
                            next_trivial_successor_propagated_concept_list,
                        backward_role_set: next_backward_role_set,
                    });
                }
            }
        }

        let _ = backward_role_set;
        true
    }

    /// Port of the dispatcher/gate prefix of
    /// `testSaturatedSuccessorModelMergable(...)`.
    ///
    /// The selected `testSingle...`/`testMultiple...` target bodies are separate
    /// port slices; this helper preserves the C++ pre-decrement gates and
    /// returns the exact downstream call payload.
    pub fn prepare_saturated_successor_model_merge_dispatch(
        &self,
        existential_indi_node: SatNodeId,
        successor_list: &[SatNodeId],
        trivial_successor_propagated_concept_list: &[(ConceptId, bool)],
        backward_role_set: &std::collections::HashSet<RoleId>,
        remaining_merging_depth: Cint64,
        remaining_merging_count: &mut Cint64,
    ) -> Option<SaturatedSuccessorMergeDispatch> {
        let remaining_merging_depth = remaining_merging_depth - 1;
        if remaining_merging_depth < 0 {
            return None;
        }
        *remaining_merging_count -= 1;
        if *remaining_merging_count < 0 {
            return None;
        }

        let kind = if successor_list.len() == 1 {
            SaturatedSuccessorMergeDispatchKind::Single
        } else {
            SaturatedSuccessorMergeDispatchKind::Multiple
        };
        Some(SaturatedSuccessorMergeDispatch {
            kind,
            existential_sat_node: existential_indi_node,
            successor_list: successor_list.to_vec(),
            trivial_successor_propagated_concept_list: trivial_successor_propagated_concept_list
                .to_vec(),
            backward_role_set: backward_role_set.clone(),
            remaining_merging_depth,
        })
    }

    /// Execute the W254 prepared recursive merge jobs through the
    /// `testSaturatedSuccessorModelMergable(...)` dispatcher prefix.
    pub fn prepare_saturated_successor_merge_job_dispatches(
        &self,
        jobs: &[SaturatedSuccessorMergeJob],
        remaining_merging_depth: Cint64,
        remaining_merging_count: &mut Cint64,
        dispatches: &mut Vec<SaturatedSuccessorMergeDispatch>,
    ) -> bool {
        for job in jobs {
            let Some(dispatch) = self.prepare_saturated_successor_model_merge_dispatch(
                job.existential_sat_node,
                &job.successor_list,
                &job.trivial_successor_propagated_concept_list,
                &job.backward_role_set,
                remaining_merging_depth,
                remaining_merging_count,
            ) else {
                return false;
            };
            dispatches.push(dispatch);
        }
        true
    }

    fn test_saturated_successor_merge_jobs_depth_first(
        &self,
        jobs: &[SaturatedSuccessorMergeJob],
        remaining_merging_depth: Cint64,
        remaining_merging_count: &mut Cint64,
        concepts: &Arena<Concept>,
        roles: &Arena<Role>,
        concept_process_datas: &Arena<ConceptProcessData>,
        concept_reference_linking_datas: &Arena<ConceptSaturationReferenceLinkingData>,
        saturation_concept_reference_linkings: &Arena<SaturationConceptReferenceLinking>,
        process_context: &ProcessContext,
        ontology_top_concept: Option<ConceptId>,
    ) -> bool {
        for job in jobs {
            if !self.test_saturated_successor_model_mergable(
                job.existential_sat_node,
                &job.successor_list,
                &job.trivial_successor_propagated_concept_list,
                &job.backward_role_set,
                remaining_merging_depth,
                remaining_merging_count,
                concepts,
                roles,
                concept_process_datas,
                concept_reference_linking_datas,
                saturation_concept_reference_linkings,
                process_context,
                ontology_top_concept,
            ) {
                return false;
            }
        }
        true
    }

    /// Port of `testSaturatedSuccessorModelMergable(...)` through the currently
    /// live single/multiple bodies.
    pub fn test_saturated_successor_model_mergable(
        &self,
        existential_indi_node: SatNodeId,
        successor_list: &[SatNodeId],
        trivial_successor_propagated_concept_list: &[(ConceptId, bool)],
        backward_role_set: &std::collections::HashSet<RoleId>,
        remaining_merging_depth: Cint64,
        remaining_merging_count: &mut Cint64,
        concepts: &Arena<Concept>,
        roles: &Arena<Role>,
        concept_process_datas: &Arena<ConceptProcessData>,
        concept_reference_linking_datas: &Arena<ConceptSaturationReferenceLinkingData>,
        saturation_concept_reference_linkings: &Arena<SaturationConceptReferenceLinking>,
        process_context: &ProcessContext,
        ontology_top_concept: Option<ConceptId>,
    ) -> bool {
        let remaining_merging_depth = remaining_merging_depth - 1;
        if remaining_merging_depth < 0 {
            return false;
        }
        *remaining_merging_count -= 1;
        if *remaining_merging_count < 0 {
            return false;
        }

        if successor_list.len() == 1 {
            self.test_single_saturated_successor_model_mergable(
                existential_indi_node,
                successor_list,
                trivial_successor_propagated_concept_list,
                backward_role_set,
                remaining_merging_depth,
                remaining_merging_count,
                concepts,
                roles,
                concept_process_datas,
                concept_reference_linking_datas,
                saturation_concept_reference_linkings,
                process_context,
                ontology_top_concept,
            )
        } else {
            self.test_multiple_saturated_successor_model_mergable(
                existential_indi_node,
                successor_list,
                trivial_successor_propagated_concept_list,
                backward_role_set,
                remaining_merging_depth,
                remaining_merging_count,
                concepts,
                roles,
                concept_process_datas,
                concept_reference_linking_datas,
                saturation_concept_reference_linkings,
                process_context,
                ontology_top_concept,
            )
        }
    }

    /// Execute an already-dispatched
    /// `testSaturatedSuccessorModelMergable(...)` branch through the currently
    /// live single/multiple wrapper bodies, then recurse into each child
    /// dispatch in produced order.
    ///
    /// The parent dispatcher gate has already consumed one depth/count step in
    /// `dispatch`; child recursive calls use `dispatch.remaining_merging_depth`
    /// and the shared `remaining_merging_count`, preserving Konclude's
    /// by-value depth and by-reference count protocol at this boundary.
    pub fn execute_saturated_successor_model_merge_dispatch(
        &self,
        dispatch: SaturatedSuccessorMergeDispatch,
        remaining_merging_count: &mut Cint64,
        concepts: &Arena<Concept>,
        roles: &Arena<Role>,
        concept_process_datas: &Arena<ConceptProcessData>,
        concept_reference_linking_datas: &Arena<ConceptSaturationReferenceLinkingData>,
        saturation_concept_reference_linkings: &Arena<SaturationConceptReferenceLinking>,
        process_context: &ProcessContext,
        ontology_top_concept: Option<ConceptId>,
    ) -> bool {
        let mut child_dispatches = Vec::new();
        let ok = match dispatch.kind {
            SaturatedSuccessorMergeDispatchKind::Single => self
                .prepare_single_saturated_successor_model_merge_dispatches(
                    dispatch.existential_sat_node,
                    &dispatch.successor_list,
                    &dispatch.trivial_successor_propagated_concept_list,
                    &dispatch.backward_role_set,
                    dispatch.remaining_merging_depth,
                    remaining_merging_count,
                    concepts,
                    roles,
                    concept_process_datas,
                    concept_reference_linking_datas,
                    saturation_concept_reference_linkings,
                    process_context,
                    ontology_top_concept,
                    &mut child_dispatches,
                ),
            SaturatedSuccessorMergeDispatchKind::Multiple => self
                .prepare_multiple_saturated_successor_model_merge_dispatches(
                    dispatch.existential_sat_node,
                    &dispatch.successor_list,
                    &dispatch.trivial_successor_propagated_concept_list,
                    &dispatch.backward_role_set,
                    dispatch.remaining_merging_depth,
                    remaining_merging_count,
                    concepts,
                    roles,
                    concept_process_datas,
                    concept_reference_linking_datas,
                    saturation_concept_reference_linkings,
                    process_context,
                    ontology_top_concept,
                    &mut child_dispatches,
                ),
        };
        if !ok {
            return false;
        }

        for child_dispatch in child_dispatches {
            if !self.execute_saturated_successor_model_merge_dispatch(
                child_dispatch,
                remaining_merging_count,
                concepts,
                roles,
                concept_process_datas,
                concept_reference_linking_datas,
                saturation_concept_reference_linkings,
                process_context,
                ontology_top_concept,
            ) {
                return false;
            }
        }
        true
    }

    /// Execute a prepared recursive merge job through the live
    /// `testSaturatedSuccessorModelMergable(...)` dispatcher/body bridge.
    pub fn execute_saturated_successor_merge_job(
        &self,
        job: &SaturatedSuccessorMergeJob,
        remaining_merging_depth: Cint64,
        remaining_merging_count: &mut Cint64,
        concepts: &Arena<Concept>,
        roles: &Arena<Role>,
        concept_process_datas: &Arena<ConceptProcessData>,
        concept_reference_linking_datas: &Arena<ConceptSaturationReferenceLinkingData>,
        saturation_concept_reference_linkings: &Arena<SaturationConceptReferenceLinking>,
        process_context: &ProcessContext,
        ontology_top_concept: Option<ConceptId>,
    ) -> bool {
        self.test_saturated_successor_model_mergable(
            job.existential_sat_node,
            &job.successor_list,
            &job.trivial_successor_propagated_concept_list,
            &job.backward_role_set,
            remaining_merging_depth,
            remaining_merging_count,
            concepts,
            roles,
            concept_process_datas,
            concept_reference_linking_datas,
            saturation_concept_reference_linkings,
            process_context,
            ontology_top_concept,
        )
    }

    fn saturation_label_set_entry_by_tag(
        process_context: &ProcessContext,
        sat_con_set: super::super::saturation::satellites::ReapplyConceptSaturationLabelSetId,
        con_tag: Cint64,
    ) -> Option<(
        super::super::saturation::satellites::ConceptSaturationDescriptorId,
        super::super::saturation::satellites::ImplicationReapplyConceptSaturationDescriptorId,
    )> {
        if sat_con_set.is_none()
            || sat_con_set.index() >= process_context.reapply_con_sat_label_set_count()
        {
            return None;
        }
        let sat_con_set_ref = process_context.reapply_con_sat_label_set(sat_con_set);
        sat_con_set_ref
            .concept_des_dep_hash
            .get(&con_tag)
            .or_else(|| {
                if sat_con_set_ref.has_additional_concept_des_dep_hash {
                    sat_con_set_ref
                        .additional_concept_des_dep_hash
                        .get(&con_tag)
                } else {
                    None
                }
            })
            .map(|data| (data.con_sat_des, data.imp_reapply_con_sat_des))
    }

    /// Port of the opening trivial-concept/substitute-resolution block in
    /// `testSingleSaturatedSuccessorModelMergable(...)`.
    pub fn prepare_single_saturated_successor_merge_state(
        &self,
        existential_indi_node: SatNodeId,
        trivial_successor_propagated_concept_list: &[(ConceptId, bool)],
        backward_role_set: &std::collections::HashSet<RoleId>,
        concepts: &Arena<Concept>,
        process_context: &ProcessContext,
    ) -> Option<SingleSaturatedSuccessorMergeState> {
        if existential_indi_node.is_none()
            || existential_indi_node.index() >= process_context.sat_node_count()
        {
            return None;
        }

        let mut sub_resolved_existential_indi_node = existential_indi_node;
        while process_context
            .sat_node(sub_resolved_existential_indi_node)
            .has_substitute_individual_node()
        {
            sub_resolved_existential_indi_node = process_context
                .sat_node(sub_resolved_existential_indi_node)
                .get_substitute_individual_node();
            if sub_resolved_existential_indi_node.is_none()
                || sub_resolved_existential_indi_node.index() >= process_context.sat_node_count()
            {
                return None;
            }
        }

        let sat_con_set = process_context
            .sat_node(sub_resolved_existential_indi_node)
            .reapply_con_sat_label_set;
        if sat_con_set.is_none()
            || sat_con_set.index() >= process_context.reapply_con_sat_label_set_count()
        {
            return None;
        }

        let mut successor_influence_concepts = Vec::new();
        for (concept, negation) in trivial_successor_propagated_concept_list.iter().copied() {
            if concept.is_none() || concept.index() >= concepts.len() {
                return None;
            }
            let concept_ref = concepts.get(concept);
            let con_op_code = concept_ref.get_operator_code();

            if negation && con_op_code == CCSUB {
                let con_tag = concept_ref.get_concept_tag();
                if let Some((con_sat_des, imp_con_sat_des)) =
                    Self::saturation_label_set_entry_by_tag(process_context, sat_con_set, con_tag)
                {
                    if con_sat_des.is_some() {
                        if con_sat_des.index() >= process_context.con_sat_desc_count() {
                            return None;
                        }
                        if process_context.con_sat_desc(con_sat_des).get_negation() != negation {
                            return None;
                        }
                    }
                    if con_sat_des.is_none() && imp_con_sat_des.is_some() {
                        return None;
                    }
                } else {
                    let mut tmp_sub_existential_indi_node = existential_indi_node;
                    while process_context
                        .sat_node(tmp_sub_existential_indi_node)
                        .has_substitute_individual_node()
                    {
                        let concept_sat_item = process_context
                            .sat_node(tmp_sub_existential_indi_node)
                            .get_saturation_concept_reference_linking();
                        if concept_sat_item.is_none()
                            || concept_sat_item.index()
                                >= process_context.extended_con_ref_linking_data_count()
                        {
                            return None;
                        }
                        let concept_sat_item_ref =
                            process_context.extended_con_ref_linking_data(concept_sat_item);
                        if concept_sat_item_ref.get_saturation_concept() == concept
                            && negation != concept_sat_item_ref.get_saturation_negation()
                        {
                            return None;
                        }
                        tmp_sub_existential_indi_node = process_context
                            .sat_node(tmp_sub_existential_indi_node)
                            .get_substitute_individual_node();
                        if tmp_sub_existential_indi_node.is_none()
                            || tmp_sub_existential_indi_node.index()
                                >= process_context.sat_node_count()
                        {
                            return None;
                        }
                    }
                }
            } else if !negation
                && (con_op_code == CCALL
                    || con_op_code == CCIMPLALL
                    || con_op_code == CCBRANCHALL
                    || con_op_code == CCAQALL
                    || con_op_code == CCIMPLAQALL
                    || con_op_code == CCBRANCHAQALL)
            {
                let role = concept_ref.get_role();
                if backward_role_set.contains(&role) {
                    return None;
                }
                for operand in concept_ref.get_operand_list() {
                    successor_influence_concepts
                        .push((role, (operand.target, operand.negated ^ negation)));
                }
            }
        }

        Some(SingleSaturatedSuccessorMergeState {
            sub_resolved_existential_sat_node: sub_resolved_existential_indi_node,
            saturation_label_set: sat_con_set,
            successor_influence_concepts,
        })
    }

    /// Port of the non-extension descriptor walk in
    /// `testSingleSaturatedSuccessorModelMergable(...)`.
    pub fn collect_single_successor_non_extension_recursive_merge_jobs(
        &self,
        existential_indi_node: SatNodeId,
        successor_list: &[SatNodeId],
        trivial_successor_propagated_concept_list: &[(ConceptId, bool)],
        state: &SingleSaturatedSuccessorMergeState,
        concepts: &Arena<Concept>,
        roles: &Arena<Role>,
        concept_process_datas: &Arena<ConceptProcessData>,
        concept_reference_linking_datas: &Arena<ConceptSaturationReferenceLinkingData>,
        saturation_concept_reference_linkings: &Arena<SaturationConceptReferenceLinking>,
        process_context: &ProcessContext,
        ontology_top_concept: Option<ConceptId>,
        jobs: &mut Vec<SaturatedSuccessorMergeJob>,
    ) -> bool {
        if existential_indi_node.is_none()
            || existential_indi_node.index() >= process_context.sat_node_count()
            || state.saturation_label_set.is_none()
            || state.saturation_label_set.index()
                >= process_context.reapply_con_sat_label_set_count()
        {
            return false;
        }

        if process_context
            .sat_node(existential_indi_node)
            .direct_status_flags
            .has_flags_code(
                IndividualSaturationProcessNodeStatusFlags::INDSUCCESSORNODEEXTENSIONS,
                false,
            )
        {
            return true;
        }

        let mut con_sat_des_it = process_context
            .reapply_con_sat_label_set(state.saturation_label_set)
            .get_concept_saturation_description_linker();
        while con_sat_des_it.is_some() {
            if con_sat_des_it.index() >= process_context.con_sat_desc_count() {
                return false;
            }
            let con_sat_des_ref = process_context.con_sat_desc(con_sat_des_it);
            let concept = con_sat_des_ref.get_concept();
            if concept.is_none() || concept.index() >= concepts.len() {
                return false;
            }
            let negated = con_sat_des_ref.get_negation();
            let concept_ref = concepts.get(concept);
            let op_code = concept_ref.get_operator_code();
            let card = concept_ref.get_parameter();
            if (!negated
                && (op_code == CCSOME || op_code == CCAQSOME || (op_code == CCATLEAST && card > 0)))
                || (negated && (op_code == CCALL || (op_code == CCATMOST && card >= 0)))
            {
                let role = concept_ref.get_role();
                let mut next_successor_list = Vec::new();
                let mut next_trivial_successor_propagated_concept_list = Vec::new();
                let mut next_backward_role_set = std::collections::HashSet::new();

                if !self.collect_successor_merging_nodes_and_concepts_for_saturation_node(
                    existential_indi_node,
                    role,
                    concepts,
                    roles,
                    concept_process_datas,
                    concept_reference_linking_datas,
                    saturation_concept_reference_linkings,
                    process_context,
                    successor_list,
                    &mut next_successor_list,
                    &mut next_trivial_successor_propagated_concept_list,
                    &mut next_backward_role_set,
                    &state.successor_influence_concepts,
                ) {
                    return false;
                }

                if !next_successor_list.is_empty()
                    || !trivial_successor_propagated_concept_list.is_empty()
                {
                    let ext_sat_indi_node = self
                        .get_existential_saturated_individual_node_for_concept(
                            concept,
                            concepts,
                            concept_process_datas,
                            concept_reference_linking_datas,
                            saturation_concept_reference_linkings,
                            process_context,
                            ontology_top_concept,
                        );
                    let Some(ext_sat_indi_node) = ext_sat_indi_node else {
                        return false;
                    };
                    next_successor_list.insert(0, ext_sat_indi_node);
                    jobs.push(SaturatedSuccessorMergeJob {
                        existential_sat_node: ext_sat_indi_node,
                        successor_list: next_successor_list,
                        trivial_successor_propagated_concept_list:
                            next_trivial_successor_propagated_concept_list,
                        backward_role_set: next_backward_role_set,
                    });
                }
            }

            con_sat_des_it = process_context
                .con_sat_desc(con_sat_des_it)
                .get_next_concept_desciptor();
        }

        true
    }

    /// Port of the linked-successor extension branch shared by
    /// `testSingleSaturatedSuccessorModelMergable(...)` and
    /// `testMultipleSaturatedSuccessorModelMergable(...)`.
    pub fn collect_linked_successor_extension_recursive_merge_jobs(
        &self,
        extension_source_indi_node: SatNodeId,
        successor_list: &[SatNodeId],
        trivial_successor_propagated_concept_list: &[(ConceptId, bool)],
        successor_influence_concepts: &[(RoleId, (ConceptId, bool))],
        concepts: &Arena<Concept>,
        roles: &Arena<Role>,
        concept_process_datas: &Arena<ConceptProcessData>,
        concept_reference_linking_datas: &Arena<ConceptSaturationReferenceLinkingData>,
        saturation_concept_reference_linkings: &Arena<SaturationConceptReferenceLinking>,
        process_context: &ProcessContext,
        jobs: &mut Vec<SaturatedSuccessorMergeJob>,
    ) -> bool {
        if extension_source_indi_node.is_none()
            || extension_source_indi_node.index() >= process_context.sat_node_count()
        {
            return false;
        }
        let source_ref = process_context.sat_node(extension_source_indi_node);
        if !source_ref.direct_status_flags.has_flags_code(
            IndividualSaturationProcessNodeStatusFlags::INDSUCCESSORNODEEXTENSIONS,
            false,
        ) {
            return true;
        }

        let ext = source_ref.indi_extension_data;
        if ext.is_none() {
            return true;
        }
        if ext.index() >= process_context.indi_sat_node_ext_data_count() {
            return false;
        }
        let linked_succ_hash = process_context
            .indi_sat_node_ext_data(ext)
            .linked_role_succ_hash;
        if linked_succ_hash.is_none() {
            return true;
        }
        if linked_succ_hash.index() >= process_context.linked_role_sat_succ_hash_count() {
            return false;
        }

        for (role, linked_succ_data) in process_context
            .linked_role_sat_succ_hash(linked_succ_hash)
            .get_linked_role_successor_hash()
            .iter()
        {
            if linked_succ_data.is_none()
                || linked_succ_data.index() >= process_context.linked_role_sat_succ_data_count()
            {
                return false;
            }
            for succ_data in process_context
                .linked_role_sat_succ_data(*linked_succ_data)
                .get_successor_node_data_map()
                .values()
                .copied()
            {
                if succ_data.is_none() || succ_data.index() >= process_context.sat_succ_data_count()
                {
                    return false;
                }
                let succ_data_ref = process_context.sat_succ_data(succ_data);
                if succ_data_ref.get_active_count() < 1 {
                    continue;
                }

                for creation_role_linker in succ_data_ref.creation_role_linker.iter() {
                    if !creation_role_linker.negated && creation_role_linker.target == *role {
                        let mut next_successor_list = Vec::new();
                        let mut next_trivial_successor_propagated_concept_list = Vec::new();
                        let mut next_backward_role_set = std::collections::HashSet::new();

                        if !self.collect_successor_merging_nodes_and_concepts_for_saturation_node(
                            extension_source_indi_node,
                            *role,
                            concepts,
                            roles,
                            concept_process_datas,
                            concept_reference_linking_datas,
                            saturation_concept_reference_linkings,
                            process_context,
                            successor_list,
                            &mut next_successor_list,
                            &mut next_trivial_successor_propagated_concept_list,
                            &mut next_backward_role_set,
                            successor_influence_concepts,
                        ) {
                            return false;
                        }

                        if !next_successor_list.is_empty()
                            || !trivial_successor_propagated_concept_list.is_empty()
                        {
                            let ext_sat_indi_node = succ_data_ref.get_successor_individual_node();
                            if ext_sat_indi_node.is_none()
                                || ext_sat_indi_node.index() >= process_context.sat_node_count()
                            {
                                return false;
                            }
                            next_successor_list.insert(0, ext_sat_indi_node);
                            jobs.push(SaturatedSuccessorMergeJob {
                                existential_sat_node: ext_sat_indi_node,
                                successor_list: next_successor_list,
                                trivial_successor_propagated_concept_list:
                                    next_trivial_successor_propagated_concept_list,
                                backward_role_set: next_backward_role_set,
                            });
                        }
                    }
                }
            }
        }

        true
    }

    /// Port-facing wrapper for the currently live slices of
    /// `testSingleSaturatedSuccessorModelMergable(...)`.
    ///
    /// The upstream method immediately recurses through
    /// `testSaturatedSuccessorModelMergable(...)` at each prepared job. Until
    /// the full recursive body is live, this wrapper preserves the C++ order and
    /// returns the dispatcher payloads created at those call sites.
    pub fn prepare_single_saturated_successor_model_merge_dispatches(
        &self,
        existential_indi_node: SatNodeId,
        successor_list: &[SatNodeId],
        trivial_successor_propagated_concept_list: &[(ConceptId, bool)],
        backward_role_set: &std::collections::HashSet<RoleId>,
        remaining_merging_depth: Cint64,
        remaining_merging_count: &mut Cint64,
        concepts: &Arena<Concept>,
        roles: &Arena<Role>,
        concept_process_datas: &Arena<ConceptProcessData>,
        concept_reference_linking_datas: &Arena<ConceptSaturationReferenceLinkingData>,
        saturation_concept_reference_linkings: &Arena<SaturationConceptReferenceLinking>,
        process_context: &ProcessContext,
        ontology_top_concept: Option<ConceptId>,
        dispatches: &mut Vec<SaturatedSuccessorMergeDispatch>,
    ) -> bool {
        let Some(state) = self.prepare_single_saturated_successor_merge_state(
            existential_indi_node,
            trivial_successor_propagated_concept_list,
            backward_role_set,
            concepts,
            process_context,
        ) else {
            return false;
        };

        let mut jobs = Vec::new();
        if process_context
            .sat_node(existential_indi_node)
            .direct_status_flags
            .has_flags_code(
                IndividualSaturationProcessNodeStatusFlags::INDSUCCESSORNODEEXTENSIONS,
                false,
            )
        {
            if !self.collect_linked_successor_extension_recursive_merge_jobs(
                existential_indi_node,
                successor_list,
                trivial_successor_propagated_concept_list,
                &state.successor_influence_concepts,
                concepts,
                roles,
                concept_process_datas,
                concept_reference_linking_datas,
                saturation_concept_reference_linkings,
                process_context,
                &mut jobs,
            ) {
                return false;
            }
        } else if !self.collect_single_successor_non_extension_recursive_merge_jobs(
            existential_indi_node,
            successor_list,
            trivial_successor_propagated_concept_list,
            &state,
            concepts,
            roles,
            concept_process_datas,
            concept_reference_linking_datas,
            saturation_concept_reference_linkings,
            process_context,
            ontology_top_concept,
            &mut jobs,
        ) {
            return false;
        }

        self.prepare_saturated_successor_merge_job_dispatches(
            &jobs,
            remaining_merging_depth,
            remaining_merging_count,
            dispatches,
        )
    }

    /// Port of `testSingleSaturatedSuccessorModelMergable(...)` through the
    /// currently live recursive job collectors, executing child jobs
    /// depth-first at the call boundary.
    pub fn test_single_saturated_successor_model_mergable(
        &self,
        existential_indi_node: SatNodeId,
        successor_list: &[SatNodeId],
        trivial_successor_propagated_concept_list: &[(ConceptId, bool)],
        backward_role_set: &std::collections::HashSet<RoleId>,
        remaining_merging_depth: Cint64,
        remaining_merging_count: &mut Cint64,
        concepts: &Arena<Concept>,
        roles: &Arena<Role>,
        concept_process_datas: &Arena<ConceptProcessData>,
        concept_reference_linking_datas: &Arena<ConceptSaturationReferenceLinkingData>,
        saturation_concept_reference_linkings: &Arena<SaturationConceptReferenceLinking>,
        process_context: &ProcessContext,
        ontology_top_concept: Option<ConceptId>,
    ) -> bool {
        let Some(state) = self.prepare_single_saturated_successor_merge_state(
            existential_indi_node,
            trivial_successor_propagated_concept_list,
            backward_role_set,
            concepts,
            process_context,
        ) else {
            return false;
        };

        let mut jobs = Vec::new();
        if process_context
            .sat_node(existential_indi_node)
            .direct_status_flags
            .has_flags_code(
                IndividualSaturationProcessNodeStatusFlags::INDSUCCESSORNODEEXTENSIONS,
                false,
            )
        {
            if !self.collect_linked_successor_extension_recursive_merge_jobs(
                existential_indi_node,
                successor_list,
                trivial_successor_propagated_concept_list,
                &state.successor_influence_concepts,
                concepts,
                roles,
                concept_process_datas,
                concept_reference_linking_datas,
                saturation_concept_reference_linkings,
                process_context,
                &mut jobs,
            ) {
                return false;
            }
        } else if !self.collect_single_successor_non_extension_recursive_merge_jobs(
            existential_indi_node,
            successor_list,
            trivial_successor_propagated_concept_list,
            &state,
            concepts,
            roles,
            concept_process_datas,
            concept_reference_linking_datas,
            saturation_concept_reference_linkings,
            process_context,
            ontology_top_concept,
            &mut jobs,
        ) {
            return false;
        }

        self.test_saturated_successor_merge_jobs_depth_first(
            &jobs,
            remaining_merging_depth,
            remaining_merging_count,
            concepts,
            roles,
            concept_process_datas,
            concept_reference_linking_datas,
            saturation_concept_reference_linkings,
            process_context,
            ontology_top_concept,
        )
    }

    /// Port-facing wrapper for the currently live slices of
    /// `testMultipleSaturatedSuccessorModelMergable(...)`.
    ///
    /// This composes the W250-W254 trigger checks/job preparation with the W258
    /// linked-successor extension branch and preserves the upstream recursive
    /// call ordering by dispatching trigger jobs before per-successor extension
    /// jobs.
    pub fn prepare_multiple_saturated_successor_model_merge_dispatches(
        &self,
        existential_indi_node: SatNodeId,
        successor_list: &[SatNodeId],
        trivial_successor_propagated_concept_list: &[(ConceptId, bool)],
        backward_role_set: &std::collections::HashSet<RoleId>,
        remaining_merging_depth: Cint64,
        remaining_merging_count: &mut Cint64,
        concepts: &Arena<Concept>,
        roles: &Arena<Role>,
        concept_process_datas: &Arena<ConceptProcessData>,
        concept_reference_linking_datas: &Arena<ConceptSaturationReferenceLinkingData>,
        saturation_concept_reference_linkings: &Arena<SaturationConceptReferenceLinking>,
        process_context: &ProcessContext,
        ontology_top_concept: Option<ConceptId>,
        dispatches: &mut Vec<SaturatedSuccessorMergeDispatch>,
    ) -> bool {
        let Some((mut concept_negation_trigger_hash, successor_influence_concepts)) = self
            .prepare_multiple_saturated_successor_merge_triggers(
                existential_indi_node,
                successor_list,
                trivial_successor_propagated_concept_list,
                backward_role_set,
                concepts,
                process_context,
            )
        else {
            return false;
        };

        if !self.merge_successor_saturation_label_triggers(
            successor_list,
            concepts,
            process_context,
            &mut concept_negation_trigger_hash,
        ) {
            return false;
        }

        let mut trigger_jobs = Vec::new();
        if !self.collect_multiple_successor_recursive_merge_jobs_from_triggers(
            &concept_negation_trigger_hash,
            successor_list,
            trivial_successor_propagated_concept_list,
            backward_role_set,
            &successor_influence_concepts,
            concepts,
            roles,
            concept_process_datas,
            concept_reference_linking_datas,
            saturation_concept_reference_linkings,
            process_context,
            ontology_top_concept,
            &mut trigger_jobs,
        ) {
            return false;
        }
        if !self.prepare_saturated_successor_merge_job_dispatches(
            &trigger_jobs,
            remaining_merging_depth,
            remaining_merging_count,
            dispatches,
        ) {
            return false;
        }

        for succ_indi_node in successor_list.iter().copied() {
            let mut extension_jobs = Vec::new();
            if !self.collect_linked_successor_extension_recursive_merge_jobs(
                succ_indi_node,
                successor_list,
                trivial_successor_propagated_concept_list,
                &successor_influence_concepts,
                concepts,
                roles,
                concept_process_datas,
                concept_reference_linking_datas,
                saturation_concept_reference_linkings,
                process_context,
                &mut extension_jobs,
            ) {
                return false;
            }
            if !self.prepare_saturated_successor_merge_job_dispatches(
                &extension_jobs,
                remaining_merging_depth,
                remaining_merging_count,
                dispatches,
            ) {
                return false;
            }
        }

        true
    }

    /// Port of `testMultipleSaturatedSuccessorModelMergable(...)` through the
    /// currently live trigger and linked-extension recursive job collectors.
    pub fn test_multiple_saturated_successor_model_mergable(
        &self,
        existential_indi_node: SatNodeId,
        successor_list: &[SatNodeId],
        trivial_successor_propagated_concept_list: &[(ConceptId, bool)],
        backward_role_set: &std::collections::HashSet<RoleId>,
        remaining_merging_depth: Cint64,
        remaining_merging_count: &mut Cint64,
        concepts: &Arena<Concept>,
        roles: &Arena<Role>,
        concept_process_datas: &Arena<ConceptProcessData>,
        concept_reference_linking_datas: &Arena<ConceptSaturationReferenceLinkingData>,
        saturation_concept_reference_linkings: &Arena<SaturationConceptReferenceLinking>,
        process_context: &ProcessContext,
        ontology_top_concept: Option<ConceptId>,
    ) -> bool {
        let Some((mut concept_negation_trigger_hash, successor_influence_concepts)) = self
            .prepare_multiple_saturated_successor_merge_triggers(
                existential_indi_node,
                successor_list,
                trivial_successor_propagated_concept_list,
                backward_role_set,
                concepts,
                process_context,
            )
        else {
            return false;
        };

        if !self.merge_successor_saturation_label_triggers(
            successor_list,
            concepts,
            process_context,
            &mut concept_negation_trigger_hash,
        ) {
            return false;
        }

        let mut trigger_jobs = Vec::new();
        if !self.collect_multiple_successor_recursive_merge_jobs_from_triggers(
            &concept_negation_trigger_hash,
            successor_list,
            trivial_successor_propagated_concept_list,
            backward_role_set,
            &successor_influence_concepts,
            concepts,
            roles,
            concept_process_datas,
            concept_reference_linking_datas,
            saturation_concept_reference_linkings,
            process_context,
            ontology_top_concept,
            &mut trigger_jobs,
        ) {
            return false;
        }
        if !self.test_saturated_successor_merge_jobs_depth_first(
            &trigger_jobs,
            remaining_merging_depth,
            remaining_merging_count,
            concepts,
            roles,
            concept_process_datas,
            concept_reference_linking_datas,
            saturation_concept_reference_linkings,
            process_context,
            ontology_top_concept,
        ) {
            return false;
        }

        for succ_indi_node in successor_list.iter().copied() {
            let mut extension_jobs = Vec::new();
            if !self.collect_linked_successor_extension_recursive_merge_jobs(
                succ_indi_node,
                successor_list,
                trivial_successor_propagated_concept_list,
                &successor_influence_concepts,
                concepts,
                roles,
                concept_process_datas,
                concept_reference_linking_datas,
                saturation_concept_reference_linkings,
                process_context,
                &mut extension_jobs,
            ) {
                return false;
            }
            if !self.test_saturated_successor_merge_jobs_depth_first(
                &extension_jobs,
                remaining_merging_depth,
                remaining_merging_count,
                concepts,
                roles,
                concept_process_datas,
                concept_reference_linking_datas,
                saturation_concept_reference_linkings,
                process_context,
                ontology_top_concept,
            ) {
                return false;
            }
        }

        true
    }

    fn collect_saturated_existentials_linked_extension_jobs(
        &self,
        indi_node: NodeId,
        saturation_indi_node: SatNodeId,
        concepts: &Arena<Concept>,
        roles: &Arena<Role>,
        concept_process_datas: &Arena<ConceptProcessData>,
        concept_reference_linking_datas: &Arena<ConceptSaturationReferenceLinkingData>,
        saturation_concept_reference_linkings: &Arena<SaturationConceptReferenceLinking>,
        process_context: &mut ProcessContext,
        jobs: &mut Vec<SaturatedSuccessorMergeJob>,
    ) -> bool {
        if saturation_indi_node.is_none()
            || saturation_indi_node.index() >= process_context.sat_node_count()
        {
            return false;
        }

        let ext = process_context
            .sat_node(saturation_indi_node)
            .indi_extension_data;
        if ext.is_none() {
            return true;
        }
        if ext.index() >= process_context.indi_sat_node_ext_data_count() {
            return false;
        }
        let linked_succ_hash = process_context
            .indi_sat_node_ext_data(ext)
            .linked_role_succ_hash;
        if linked_succ_hash.is_none() {
            return true;
        }
        if linked_succ_hash.index() >= process_context.linked_role_sat_succ_hash_count() {
            return false;
        }

        let mut candidates = Vec::new();
        for (role, linked_succ_data) in process_context
            .linked_role_sat_succ_hash(linked_succ_hash)
            .get_linked_role_successor_hash()
            .iter()
        {
            if linked_succ_data.is_none()
                || linked_succ_data.index() >= process_context.linked_role_sat_succ_data_count()
            {
                return false;
            }
            for succ_data in process_context
                .linked_role_sat_succ_data(*linked_succ_data)
                .get_successor_node_data_map()
                .values()
                .copied()
            {
                if succ_data.is_none() || succ_data.index() >= process_context.sat_succ_data_count()
                {
                    return false;
                }
                let succ_data_ref = process_context.sat_succ_data(succ_data);
                if succ_data_ref.get_active_count() < 1 {
                    continue;
                }
                for creation_role_linker in succ_data_ref.creation_role_linker.iter() {
                    if !creation_role_linker.negated && creation_role_linker.target == *role {
                        let ext_sat_indi_node = succ_data_ref.get_successor_individual_node();
                        if ext_sat_indi_node.is_none()
                            || ext_sat_indi_node.index() >= process_context.sat_node_count()
                        {
                            return false;
                        }
                        candidates.push((*role, ext_sat_indi_node));
                    }
                }
            }
        }

        for (role, ext_sat_indi_node) in candidates {
            let mut successor_list = Vec::new();
            let mut trivial_successor_propagated_concept_list = Vec::new();
            let mut backward_role_set = std::collections::HashSet::new();

            if !self.collect_successor_merging_nodes_and_concepts_for_completion_node(
                indi_node,
                role,
                concepts,
                roles,
                concept_process_datas,
                concept_reference_linking_datas,
                saturation_concept_reference_linkings,
                process_context,
                &mut successor_list,
                &mut trivial_successor_propagated_concept_list,
                &mut backward_role_set,
            ) {
                return false;
            }

            if !successor_list.is_empty() || !trivial_successor_propagated_concept_list.is_empty() {
                successor_list.insert(0, ext_sat_indi_node);
                jobs.push(SaturatedSuccessorMergeJob {
                    existential_sat_node: ext_sat_indi_node,
                    successor_list,
                    trivial_successor_propagated_concept_list,
                    backward_role_set,
                });
            }
        }

        true
    }

    /// Port-facing wrapper for the currently live recursive-call preparation in
    /// `testSaturatedExistentialsModelMergable(...)`.
    ///
    /// Konclude initializes `remainingMergingDepth` to 5 and
    /// `remainingMergingCount` to 100 locally, then calls
    /// `testSaturatedSuccessorModelMergable(...)` at each collected existential
    /// branch. This wrapper keeps those budgets local and returns the dispatcher
    /// payloads at the recursive call sites.
    pub fn prepare_saturated_existentials_model_merge_dispatches(
        &self,
        indi_node: NodeId,
        saturation_indi_node: SatNodeId,
        concepts: &Arena<Concept>,
        roles: &Arena<Role>,
        concept_process_datas: &Arena<ConceptProcessData>,
        concept_reference_linking_datas: &Arena<ConceptSaturationReferenceLinkingData>,
        saturation_concept_reference_linkings: &Arena<SaturationConceptReferenceLinking>,
        process_context: &mut ProcessContext,
        ontology_top_concept: Option<ConceptId>,
        dispatches: &mut Vec<SaturatedSuccessorMergeDispatch>,
    ) -> bool {
        if saturation_indi_node.is_none()
            || saturation_indi_node.index() >= process_context.sat_node_count()
        {
            return false;
        }

        let mut remaining_merging_depth = 5;
        let mut remaining_merging_count = 100;
        let mut jobs = Vec::new();

        if process_context
            .sat_node(saturation_indi_node)
            .direct_status_flags
            .has_flags_code(
                IndividualSaturationProcessNodeStatusFlags::INDSUCCESSORNODEEXTENSIONS,
                false,
            )
        {
            if !self.collect_saturated_existentials_linked_extension_jobs(
                indi_node,
                saturation_indi_node,
                concepts,
                roles,
                concept_process_datas,
                concept_reference_linking_datas,
                saturation_concept_reference_linkings,
                process_context,
                &mut jobs,
            ) {
                return false;
            }
        } else {
            let saturated_con_set = process_context
                .sat_node(saturation_indi_node)
                .reapply_con_sat_label_set;
            if saturated_con_set.is_none()
                || saturated_con_set.index() >= process_context.reapply_con_sat_label_set_count()
            {
                return false;
            }

            let mut con_sat_des_it = process_context
                .reapply_con_sat_label_set(saturated_con_set)
                .get_concept_saturation_description_linker();
            while con_sat_des_it.is_some() {
                if con_sat_des_it.index() >= process_context.con_sat_desc_count() {
                    return false;
                }
                let con_sat_des_ref = process_context.con_sat_desc(con_sat_des_it);
                let concept = con_sat_des_ref.get_concept();
                let negated = con_sat_des_ref.get_negation();
                if concept.is_none() || concept.index() >= concepts.len() {
                    return false;
                }
                let concept_ref = concepts.get(concept);
                let op_code = concept_ref.get_operator_code();
                let card = concept_ref.get_parameter();
                if (!negated
                    && (op_code == CCSOME
                        || op_code == CCAQSOME
                        || (op_code == CCATLEAST && card > 0)))
                    || (negated && (op_code == CCALL || (op_code == CCATMOST && card >= 0)))
                {
                    let role = concept_ref.get_role();
                    let mut successor_list = Vec::new();
                    let mut trivial_successor_propagated_concept_list = Vec::new();
                    let mut backward_role_set = std::collections::HashSet::new();

                    if !self.collect_successor_merging_nodes_and_concepts_for_completion_node(
                        indi_node,
                        role,
                        concepts,
                        roles,
                        concept_process_datas,
                        concept_reference_linking_datas,
                        saturation_concept_reference_linkings,
                        process_context,
                        &mut successor_list,
                        &mut trivial_successor_propagated_concept_list,
                        &mut backward_role_set,
                    ) {
                        return false;
                    }

                    if !successor_list.is_empty()
                        || !trivial_successor_propagated_concept_list.is_empty()
                    {
                        let ext_sat_indi_node = self
                            .get_existential_saturated_individual_node_for_concept(
                                concept,
                                concepts,
                                concept_process_datas,
                                concept_reference_linking_datas,
                                saturation_concept_reference_linkings,
                                process_context,
                                ontology_top_concept,
                            );
                        let Some(ext_sat_indi_node) = ext_sat_indi_node else {
                            return false;
                        };
                        successor_list.insert(0, ext_sat_indi_node);
                        jobs.push(SaturatedSuccessorMergeJob {
                            existential_sat_node: ext_sat_indi_node,
                            successor_list,
                            trivial_successor_propagated_concept_list,
                            backward_role_set,
                        });
                    }
                }

                con_sat_des_it = process_context
                    .con_sat_desc(con_sat_des_it)
                    .get_next_concept_desciptor();
            }
        }

        self.prepare_saturated_successor_merge_job_dispatches(
            &jobs,
            remaining_merging_depth,
            &mut remaining_merging_count,
            dispatches,
        )
    }

    /// Port of `testSaturatedExistentialsModelMergable(...)` through the live
    /// W262 successor-model executor.
    pub fn test_saturated_existentials_model_mergable(
        &self,
        indi_node: NodeId,
        saturation_indi_node: SatNodeId,
        concepts: &Arena<Concept>,
        roles: &Arena<Role>,
        concept_process_datas: &Arena<ConceptProcessData>,
        concept_reference_linking_datas: &Arena<ConceptSaturationReferenceLinkingData>,
        saturation_concept_reference_linkings: &Arena<SaturationConceptReferenceLinking>,
        process_context: &mut ProcessContext,
        ontology_top_concept: Option<ConceptId>,
    ) -> bool {
        if saturation_indi_node.is_none()
            || saturation_indi_node.index() >= process_context.sat_node_count()
        {
            return false;
        }

        let remaining_merging_depth = 5;
        let mut remaining_merging_count = 100;
        let mut jobs = Vec::new();

        if process_context
            .sat_node(saturation_indi_node)
            .direct_status_flags
            .has_flags_code(
                IndividualSaturationProcessNodeStatusFlags::INDSUCCESSORNODEEXTENSIONS,
                false,
            )
        {
            if !self.collect_saturated_existentials_linked_extension_jobs(
                indi_node,
                saturation_indi_node,
                concepts,
                roles,
                concept_process_datas,
                concept_reference_linking_datas,
                saturation_concept_reference_linkings,
                process_context,
                &mut jobs,
            ) {
                return false;
            }
        } else {
            let saturated_con_set = process_context
                .sat_node(saturation_indi_node)
                .reapply_con_sat_label_set;
            if saturated_con_set.is_none()
                || saturated_con_set.index() >= process_context.reapply_con_sat_label_set_count()
            {
                return false;
            }

            let mut con_sat_des_it = process_context
                .reapply_con_sat_label_set(saturated_con_set)
                .get_concept_saturation_description_linker();
            while con_sat_des_it.is_some() {
                if con_sat_des_it.index() >= process_context.con_sat_desc_count() {
                    return false;
                }
                let con_sat_des_ref = process_context.con_sat_desc(con_sat_des_it);
                let concept = con_sat_des_ref.get_concept();
                let negated = con_sat_des_ref.get_negation();
                if concept.is_none() || concept.index() >= concepts.len() {
                    return false;
                }
                let concept_ref = concepts.get(concept);
                let op_code = concept_ref.get_operator_code();
                let card = concept_ref.get_parameter();
                if (!negated
                    && (op_code == CCSOME
                        || op_code == CCAQSOME
                        || (op_code == CCATLEAST && card > 0)))
                    || (negated && (op_code == CCALL || (op_code == CCATMOST && card >= 0)))
                {
                    let role = concept_ref.get_role();
                    let mut successor_list = Vec::new();
                    let mut trivial_successor_propagated_concept_list = Vec::new();
                    let mut backward_role_set = std::collections::HashSet::new();

                    if !self.collect_successor_merging_nodes_and_concepts_for_completion_node(
                        indi_node,
                        role,
                        concepts,
                        roles,
                        concept_process_datas,
                        concept_reference_linking_datas,
                        saturation_concept_reference_linkings,
                        process_context,
                        &mut successor_list,
                        &mut trivial_successor_propagated_concept_list,
                        &mut backward_role_set,
                    ) {
                        return false;
                    }

                    if !successor_list.is_empty()
                        || !trivial_successor_propagated_concept_list.is_empty()
                    {
                        let ext_sat_indi_node = self
                            .get_existential_saturated_individual_node_for_concept(
                                concept,
                                concepts,
                                concept_process_datas,
                                concept_reference_linking_datas,
                                saturation_concept_reference_linkings,
                                process_context,
                                ontology_top_concept,
                            );
                        let Some(ext_sat_indi_node) = ext_sat_indi_node else {
                            return false;
                        };
                        successor_list.insert(0, ext_sat_indi_node);
                        jobs.push(SaturatedSuccessorMergeJob {
                            existential_sat_node: ext_sat_indi_node,
                            successor_list,
                            trivial_successor_propagated_concept_list,
                            backward_role_set,
                        });
                    }
                }

                con_sat_des_it = process_context
                    .con_sat_desc(con_sat_des_it)
                    .get_next_concept_desciptor();
            }
        }

        self.test_saturated_successor_merge_jobs_depth_first(
            &jobs,
            remaining_merging_depth,
            &mut remaining_merging_count,
            concepts,
            roles,
            concept_process_datas,
            concept_reference_linking_datas,
            saturation_concept_reference_linkings,
            process_context,
            ontology_top_concept,
        )
    }

    /// Port of the completed/status-flag gate at the start of
    /// `testSubsumerCandidatePossibleWithMergedSaturatedModel(...)`.
    ///
    /// The downstream concept-set, role-successor, and existential saturated
    /// model merge probes remain separate; this helper only answers whether the
    /// saturated node reaches those probes.
    pub fn is_saturated_individual_node_merge_test_eligible(
        &self,
        process_context: &ProcessContext,
        sat_node: SatNodeId,
    ) -> bool {
        if sat_node.is_none() || sat_node.index() >= process_context.sat_node_count() {
            return false;
        }
        let sat_node_ref = process_context.sat_node(sat_node);
        if !sat_node_ref.is_completed() {
            return false;
        }
        let problematic_flags =
            IndividualSaturationProcessNodeStatusFlags::INDSATFLAGCARDINALITYPROPLEMATIC
                | IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT
                | IndividualSaturationProcessNodeStatusFlags::INDSATFLAGNOMINALCONNECTION;
        !sat_node_ref
            .indirect_status_flags
            .has_flags_code(problematic_flags, false)
    }

    fn is_saturated_successor_merge_dependency_eligible(
        process_context: &ProcessContext,
        sat_node: SatNodeId,
    ) -> bool {
        if sat_node.is_none() || sat_node.index() >= process_context.sat_node_count() {
            return false;
        }
        let sat_node_ref = process_context.sat_node(sat_node);
        if !sat_node_ref.is_completed() {
            return false;
        }
        let problematic_flags =
            IndividualSaturationProcessNodeStatusFlags::INDSATFLAGCARDINALITYPROPLEMATIC
                | IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT
                | IndividualSaturationProcessNodeStatusFlags::INDSATFLAGCLASHED
                | IndividualSaturationProcessNodeStatusFlags::INDSATFLAGNOMINALCONNECTION;
        !sat_node_ref
            .indirect_status_flags
            .has_flags_code(problematic_flags, false)
    }

    /// Resolve the saturated individual for a concept and apply Konclude's
    /// initial merge-test eligibility gate.
    pub fn get_merge_test_eligible_saturated_individual_node_for_concept(
        &self,
        concept: ConceptId,
        concept_negation: bool,
        concepts: &Arena<Concept>,
        concept_process_datas: &Arena<ConceptProcessData>,
        concept_reference_linking_datas: &Arena<ConceptSaturationReferenceLinkingData>,
        saturation_concept_reference_linkings: &Arena<SaturationConceptReferenceLinking>,
        process_context: &ProcessContext,
    ) -> Option<SatNodeId> {
        let sat_node = self.get_saturated_individual_node_for_concept(
            concept,
            concept_negation,
            concepts,
            concept_process_datas,
            concept_reference_linking_datas,
            saturation_concept_reference_linkings,
            process_context,
        )?;
        self.is_saturated_individual_node_merge_test_eligible(process_context, sat_node)
            .then_some(sat_node)
    }

    /// Port of
    /// `CSatisfiableTaskClassificationMessageAnalyser::testConceptSetWithSaturatedModelMergable`.
    pub fn test_concept_set_with_saturated_model_mergable(
        &self,
        process_context: &ProcessContext,
        indi_node: NodeId,
        saturation_indi_node: SatNodeId,
    ) -> SaturatedConceptSetMergeResult {
        if indi_node.is_none()
            || indi_node.index() >= process_context.node_count()
            || saturation_indi_node.is_none()
            || saturation_indi_node.index() >= process_context.sat_node_count()
        {
            return SaturatedConceptSetMergeResult {
                mergable: false,
                clashed: false,
            };
        }

        let saturated_con_set = process_context
            .sat_node(saturation_indi_node)
            .reapply_con_sat_label_set;
        let con_set = process_context.node(indi_node).use_reapply_con_label_set;
        let mut merged_concepts_clashed = process_context
            .sat_node(saturation_indi_node)
            .indirect_status_flags
            .has_flags_code(
                IndividualSaturationProcessNodeStatusFlags::INDSATFLAGCLASHED,
                false,
            );

        if saturated_con_set.is_none()
            || saturated_con_set.index() >= process_context.reapply_con_sat_label_set_count()
            || con_set.is_none()
            || con_set.index() >= process_context.label_set_count()
        {
            return SaturatedConceptSetMergeResult {
                mergable: false,
                clashed: false,
            };
        }

        let mut sat_con_set_it = process_context
            .reapply_con_sat_label_set(saturated_con_set)
            .get_iterator(true, true);
        while sat_con_set_it.has_next() && !merged_concepts_clashed {
            let data_tag = sat_con_set_it.get_data_tag();
            let sat_con_des = sat_con_set_it.get_concept_saturation_descriptor();
            let sat_reapply_des =
                sat_con_set_it.get_implication_reapply_concept_saturation_descriptor();

            let mut con_des = ConDescId::NONE;
            let mut dep_track_point = TrackPointId::NONE;
            let mut reapply_queue_present = false;
            let mut reapply_queue_empty = true;
            if process_context
                .label_set(con_set)
                .get_concept_descriptor_or_reapply_queue_state_by_tag(
                    data_tag,
                    &mut con_des,
                    &mut dep_track_point,
                    &mut reapply_queue_present,
                    &mut reapply_queue_empty,
                )
            {
                if con_des.is_some() && sat_con_des.is_some() {
                    if process_context.con_desc(con_des).is_negated()
                        != process_context.con_sat_desc(sat_con_des).get_negation()
                    {
                        merged_concepts_clashed = true;
                    }
                } else if con_des.is_some() {
                    if !process_context.con_desc(con_des).is_negated() && sat_reapply_des.is_some()
                    {
                        return SaturatedConceptSetMergeResult {
                            mergable: false,
                            clashed: false,
                        };
                    }
                } else if sat_con_des.is_some()
                    && !process_context.con_sat_desc(sat_con_des).get_negation()
                    && reapply_queue_present
                    && !reapply_queue_empty
                {
                    return SaturatedConceptSetMergeResult {
                        mergable: false,
                        clashed: false,
                    };
                }
            }

            sat_con_set_it.move_next();
        }

        SaturatedConceptSetMergeResult {
            mergable: true,
            clashed: merged_concepts_clashed,
        }
    }

    /// Port of
    /// `CSatisfiableTaskClassificationMessageAnalyser::testRoleSuccessorsWithSaturatedModelMergable`.
    pub fn test_role_successors_with_saturated_model_mergable(
        &self,
        process_context: &ProcessContext,
        concepts: &Arena<Concept>,
        indi_node: NodeId,
        saturation_indi_node: SatNodeId,
    ) -> bool {
        if indi_node.is_none()
            || indi_node.index() >= process_context.node_count()
            || saturation_indi_node.is_none()
            || saturation_indi_node.index() >= process_context.sat_node_count()
        {
            return false;
        }

        let role_succ_hash = process_context.node(indi_node).use_reapply_role_succ_hash;
        let con_set = process_context.node(indi_node).use_reapply_con_label_set;
        let role_back_prop_hash = process_context
            .sat_node(saturation_indi_node)
            .role_back_prop_hash;

        if role_succ_hash.is_some() && role_back_prop_hash.is_some() {
            for (role, back_prop_data) in process_context
                .role_backward_sat_prop_hash(role_back_prop_hash)
                .get_role_backward_propagation_data_hash()
            {
                let mut reapply_linker = back_prop_data.reapply_linker;
                if reapply_linker.is_some() {
                    let role_succ_it = process_context
                        .role_succ_hash_role_successor_link_iterator_count(
                            role_succ_hash,
                            *role,
                            None,
                        );
                    if role_succ_it.has_next() {
                        while reapply_linker.is_some() {
                            let con_sat_des = process_context
                                .backward_sat_prop_reapply_desc(reapply_linker)
                                .get_reapply_concept_saturation_descriptor();
                            if con_sat_des.is_none() {
                                return false;
                            }
                            let con_sat_des_ref = process_context.con_sat_desc(con_sat_des);
                            let concept = con_sat_des_ref.get_concept();
                            let negation = con_sat_des_ref.get_negation();
                            if con_set.is_none()
                                || !Self::label_set_contains_concept_resolved(
                                    process_context,
                                    concepts,
                                    con_set,
                                    concept,
                                    negation,
                                )
                            {
                                let mut role_succ2_it = role_succ_it.clone();
                                while role_succ2_it.has_next() {
                                    let succ_link = role_succ2_it.next(true);
                                    let succ_indi = Self::successor_node_for_link(
                                        process_context,
                                        indi_node,
                                        succ_link,
                                    );
                                    let Some(succ_indi) = succ_indi else {
                                        return false;
                                    };
                                    let succ_con_set =
                                        process_context.node(succ_indi).use_reapply_con_label_set;
                                    if concept.is_none() || concept.index() >= concepts.len() {
                                        return false;
                                    }
                                    for op_con in concepts.get(concept).get_operand_list() {
                                        let op_concept = op_con.target;
                                        let op_negation = con_sat_des_ref.get_negation() ^ negation;
                                        if succ_con_set.is_none()
                                            || !Self::label_set_contains_concept_resolved(
                                                process_context,
                                                concepts,
                                                succ_con_set,
                                                op_concept,
                                                op_negation,
                                            )
                                        {
                                            return false;
                                        }
                                    }
                                }
                            }
                            reapply_linker = process_context
                                .backward_sat_prop_reapply_desc(reapply_linker)
                                .get_next();
                        }
                    }
                }
            }
        }
        true
    }

    /// Port-facing wrapper for
    /// `testSubsumerCandidatePossibleWithMergedSaturatedModel(...)`.
    ///
    /// The final existential probe still returns the W260 dispatcher payloads
    /// instead of executing the recursive successor merge bodies, but the caller
    /// gate/order and `mergeSatisfieableFlag` behaviour match the C++ method.
    pub fn prepare_subsumer_candidate_merged_saturated_model_dispatches(
        &self,
        indi_node: NodeId,
        test_concept: ConceptId,
        negation: bool,
        merge_satisfiable_flag: &mut bool,
        concepts: &Arena<Concept>,
        roles: &Arena<Role>,
        concept_process_datas: &Arena<ConceptProcessData>,
        concept_reference_linking_datas: &Arena<ConceptSaturationReferenceLinkingData>,
        saturation_concept_reference_linkings: &Arena<SaturationConceptReferenceLinking>,
        process_context: &mut ProcessContext,
        ontology_top_concept: Option<ConceptId>,
        dispatches: &mut Vec<SaturatedSuccessorMergeDispatch>,
    ) -> bool {
        let Some(saturation_indi_node) = self.get_saturated_individual_node_for_concept(
            test_concept,
            negation,
            concepts,
            concept_process_datas,
            concept_reference_linking_datas,
            saturation_concept_reference_linkings,
            process_context,
        ) else {
            return false;
        };

        if !self
            .is_saturated_individual_node_merge_test_eligible(process_context, saturation_indi_node)
        {
            return false;
        }

        let concept_set_result = self.test_concept_set_with_saturated_model_mergable(
            process_context,
            indi_node,
            saturation_indi_node,
        );
        if !concept_set_result.mergable {
            return false;
        }
        if concept_set_result.clashed {
            *merge_satisfiable_flag = false;
            return true;
        }

        if !self.test_role_successors_with_saturated_model_mergable(
            process_context,
            concepts,
            indi_node,
            saturation_indi_node,
        ) {
            return false;
        }

        if !self.prepare_saturated_existentials_model_merge_dispatches(
            indi_node,
            saturation_indi_node,
            concepts,
            roles,
            concept_process_datas,
            concept_reference_linking_datas,
            saturation_concept_reference_linkings,
            process_context,
            ontology_top_concept,
            dispatches,
        ) {
            return false;
        }

        *merge_satisfiable_flag = true;
        true
    }

    /// Port of
    /// `testSubsumerCandidatePossibleWithMergedSaturatedModel(...)` through the
    /// live W263 existential/successor-model execution path.
    pub fn test_subsumer_candidate_possible_with_merged_saturated_model(
        &self,
        indi_node: NodeId,
        test_concept: ConceptId,
        negation: bool,
        merge_satisfiable_flag: &mut bool,
        concepts: &Arena<Concept>,
        roles: &Arena<Role>,
        concept_process_datas: &Arena<ConceptProcessData>,
        concept_reference_linking_datas: &Arena<ConceptSaturationReferenceLinkingData>,
        saturation_concept_reference_linkings: &Arena<SaturationConceptReferenceLinking>,
        process_context: &mut ProcessContext,
        ontology_top_concept: Option<ConceptId>,
    ) -> bool {
        let Some(saturation_indi_node) = self.get_saturated_individual_node_for_concept(
            test_concept,
            negation,
            concepts,
            concept_process_datas,
            concept_reference_linking_datas,
            saturation_concept_reference_linkings,
            process_context,
        ) else {
            return false;
        };

        if !self
            .is_saturated_individual_node_merge_test_eligible(process_context, saturation_indi_node)
        {
            return false;
        }

        let concept_set_result = self.test_concept_set_with_saturated_model_mergable(
            process_context,
            indi_node,
            saturation_indi_node,
        );
        if !concept_set_result.mergable {
            return false;
        }
        if concept_set_result.clashed {
            *merge_satisfiable_flag = false;
            return true;
        }

        if !self.test_role_successors_with_saturated_model_mergable(
            process_context,
            concepts,
            indi_node,
            saturation_indi_node,
        ) {
            return false;
        }

        if !self.test_saturated_existentials_model_mergable(
            indi_node,
            saturation_indi_node,
            concepts,
            roles,
            concept_process_datas,
            concept_reference_linking_datas,
            saturation_concept_reference_linkings,
            process_context,
            ontology_top_concept,
        ) {
            return false;
        }

        *merge_satisfiable_flag = true;
        true
    }

    /// Port of the simple
    /// `testSubsumerCandidatePossibleWithMergedSaturatedModel(indiNode, equivConcept, ...)`
    /// overload used by equivalent candidate/non-candidate possible-subsumer
    /// extraction.
    pub fn test_equivalent_subsumer_candidate_possible_with_merged_saturated_model(
        &self,
        indi_node: NodeId,
        equiv_concept: ConceptId,
        concepts: &Arena<Concept>,
        roles: &Arena<Role>,
        concept_process_datas: &Arena<ConceptProcessData>,
        concept_reference_linking_datas: &Arena<ConceptSaturationReferenceLinkingData>,
        saturation_concept_reference_linkings: &Arena<SaturationConceptReferenceLinking>,
        process_context: &mut ProcessContext,
        ontology_top_concept: Option<ConceptId>,
    ) -> bool {
        if Self::operator_code(equiv_concept, concepts) == CCEQ {
            let mut alternatives_set = Vec::new();
            let mut test_saturated_merged_hash = std::collections::HashMap::new();
            let mut one_merge_satisfiable_flag = false;
            let mut all_merge_unsatisfiable_flag = true;
            if self.collect_equivalence_concept_alternatives(
                indi_node,
                equiv_concept,
                true,
                &mut alternatives_set,
                &mut test_saturated_merged_hash,
                &mut one_merge_satisfiable_flag,
                &mut all_merge_unsatisfiable_flag,
                concepts,
                roles,
                concept_process_datas,
                concept_reference_linking_datas,
                saturation_concept_reference_linkings,
                process_context,
                ontology_top_concept,
            ) {
                if one_merge_satisfiable_flag {
                    return false;
                }
            } else if self.test_equivalence_concept_alternatives(
                indi_node,
                &alternatives_set,
                &mut test_saturated_merged_hash,
                &mut one_merge_satisfiable_flag,
                &mut all_merge_unsatisfiable_flag,
                concepts,
                roles,
                concept_process_datas,
                concept_reference_linking_datas,
                saturation_concept_reference_linkings,
                process_context,
                ontology_top_concept,
            ) && one_merge_satisfiable_flag
            {
                return false;
            }
        }
        true
    }

    /// Port of the equivalent-non-candidate extraction block in
    /// `extractPossibleSubsumptionInformation`.
    pub fn collect_equivalent_non_candidate_possible_subsumers(
        &self,
        indi_node: NodeId,
        ontology: &OntologyArenas,
        concepts: &Arena<Concept>,
        roles: &Arena<Role>,
        concept_process_datas: &Arena<ConceptProcessData>,
        concept_reference_linking_datas: &Arena<ConceptSaturationReferenceLinkingData>,
        saturation_concept_reference_linkings: &Arena<SaturationConceptReferenceLinking>,
        process_context: &mut ProcessContext,
        ontology_top_concept: Option<ConceptId>,
    ) -> (bool, Vec<ConceptId>) {
        let Some(equivalent_non_candidate_set) =
            ontology.get_equivalent_concept_non_candidate_set()
        else {
            return (false, Vec::new());
        };

        let mut possible_subsumers: Vec<_> = equivalent_non_candidate_set.iter().copied().collect();
        possible_subsumers
            .sort_by_key(|concept| (Self::concept_tag(*concept, concepts), concept.index()));
        possible_subsumers.retain(|eq_concept| {
            self.test_equivalent_subsumer_candidate_possible_with_merged_saturated_model(
                indi_node,
                *eq_concept,
                concepts,
                roles,
                concept_process_datas,
                concept_reference_linking_datas,
                saturation_concept_reference_linkings,
                process_context,
                ontology_top_concept,
            )
        });
        (true, possible_subsumers)
    }

    /// Port of `collectEquivalenceConceptAlternatives(...)`.
    pub fn collect_equivalence_concept_alternatives(
        &self,
        indi_node: NodeId,
        test_concept: ConceptId,
        test_concept_negation: bool,
        alternatives_set: &mut Vec<(ConceptId, bool)>,
        test_saturated_merged_hash: &mut std::collections::HashMap<
            (ConceptId, bool),
            SaturatedMergedTestItem,
        >,
        one_merge_satisfiable_flag: &mut bool,
        all_merge_unsatisfiable_flag: &mut bool,
        concepts: &Arena<Concept>,
        roles: &Arena<Role>,
        concept_process_datas: &Arena<ConceptProcessData>,
        concept_reference_linking_datas: &Arena<ConceptSaturationReferenceLinkingData>,
        saturation_concept_reference_linkings: &Arena<SaturationConceptReferenceLinking>,
        process_context: &mut ProcessContext,
        ontology_top_concept: Option<ConceptId>,
    ) -> bool {
        if indi_node.is_none()
            || indi_node.index() >= process_context.node_count()
            || test_concept.is_none()
            || test_concept.index() >= concepts.len()
        {
            return false;
        }

        let con_set = process_context.node(indi_node).use_reapply_con_label_set;
        if con_set.is_none() || con_set.index() >= process_context.label_set_count() {
            return false;
        }

        *all_merge_unsatisfiable_flag = true;
        let mut alternative_exp_list = std::collections::VecDeque::new();
        let mut alternative_exp_set = std::collections::HashSet::new();
        let initial_pair = (test_concept, test_concept_negation);
        alternative_exp_list.push_back(initial_pair);
        alternative_exp_set.insert(initial_pair);

        while let Some((concept, negation)) = alternative_exp_list.pop_front() {
            if concept.is_none() || concept.index() >= concepts.len() {
                return false;
            }
            let concept_ref = concepts.get(concept);
            let con_op_code = concept_ref.get_operator_code();

            if (negation && (con_op_code == CCEQ || con_op_code == CCAND))
                || (!negation && con_op_code == CCOR)
            {
                for operand_linker in concept_ref.get_operand_list() {
                    let operand_pair = (operand_linker.target, operand_linker.negated ^ negation);
                    if alternative_exp_set.insert(operand_pair) {
                        alternative_exp_list.push_back(operand_pair);
                    }
                }
            } else if con_op_code == CCAQCHOOCE {
                for operand_linker in concept_ref.get_operand_list() {
                    let operand_negation = operand_linker.negated;
                    if negation == operand_negation {
                        let operand_pair = (operand_linker.target, operand_negation);
                        if alternative_exp_set.insert(operand_pair) {
                            alternative_exp_list.push_back(operand_pair);
                        }
                    }
                }
            } else if (negation && con_op_code == CCALL)
                || (!negation && (con_op_code == CCSOME || con_op_code == CCAQSOME))
            {
                if let Some(contains_negation) = Self::label_set_concept_negation_resolved(
                    process_context,
                    concepts,
                    con_set,
                    concept,
                ) {
                    if contains_negation == negation {
                        *one_merge_satisfiable_flag = true;
                        *all_merge_unsatisfiable_flag = false;
                        return true;
                    }
                } else {
                    let saturated_merged_test_item = test_saturated_merged_hash
                        .entry((concept, negation))
                        .or_default();
                    if saturated_merged_test_item.successfully_merged {
                        if saturated_merged_test_item.satisfiable_merged {
                            *one_merge_satisfiable_flag = true;
                            *all_merge_unsatisfiable_flag = false;
                            return true;
                        }
                    } else if !alternatives_set.contains(&(concept, negation)) {
                        alternatives_set.push((concept, negation));
                    }
                }
            } else {
                if let Some(contains_negation) = Self::label_set_concept_negation_resolved(
                    process_context,
                    concepts,
                    con_set,
                    concept,
                ) {
                    if contains_negation == negation {
                        *one_merge_satisfiable_flag = true;
                        *all_merge_unsatisfiable_flag = false;
                        return true;
                    }
                } else {
                    *all_merge_unsatisfiable_flag = false;
                }
            }
        }

        if alternatives_set.is_empty() && *all_merge_unsatisfiable_flag {
            return true;
        }

        self.test_equivalence_concept_alternatives(
            indi_node,
            alternatives_set,
            test_saturated_merged_hash,
            one_merge_satisfiable_flag,
            all_merge_unsatisfiable_flag,
            concepts,
            roles,
            concept_process_datas,
            concept_reference_linking_datas,
            saturation_concept_reference_linkings,
            process_context,
            ontology_top_concept,
        )
    }

    /// Port of `checkCanHaveClashWithModel(...)`.
    pub fn check_can_have_clash_with_model(
        &self,
        indi_node: NodeId,
        concept: ConceptId,
        negated: bool,
        depth: Cint64,
        tested_individuals_set: &mut std::collections::HashSet<NodeId>,
        last_node: NodeId,
        concepts: &Arena<Concept>,
        process_context: &ProcessContext,
    ) -> ModelClashCheckResult {
        const MAX_POSSIBLE_SUBSUMER_NEGATION_CHECKING_DEPTH: Cint64 = 5;

        if depth > MAX_POSSIBLE_SUBSUMER_NEGATION_CHECKING_DEPTH
            || indi_node.is_none()
            || indi_node.index() >= process_context.node_count()
            || concept.is_none()
            || concept.index() >= concepts.len()
        {
            return ModelClashCheckResult {
                unknown: true,
                ..Default::default()
            };
        }

        let node_ref = process_context.node(indi_node);
        if node_ref.has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_INVALIDATEBLOCKERFLAGSCOMPINATION,
        ) || (last_node != indi_node && tested_individuals_set.contains(&indi_node))
        {
            return ModelClashCheckResult {
                unknown: true,
                ..Default::default()
            };
        }
        if last_node != indi_node {
            tested_individuals_set.insert(indi_node);
        }

        let label_set = node_ref.use_reapply_con_label_set;
        if let Some((con_des, contains_negated, dep_track_point, reapply_queue_present)) =
            Self::label_set_concept_model_entry_resolved(
                process_context,
                concepts,
                label_set,
                concept,
            )
        {
            if con_des.is_some() {
                if contains_negated ^ negated {
                    if dep_track_point.is_none()
                        || process_context
                            .track_point(dep_track_point)
                            .get_branching_tag()
                            > 0
                    {
                        return ModelClashCheckResult {
                            unknown: true,
                            ..Default::default()
                        };
                    }
                    return ModelClashCheckResult {
                        clash_found: true,
                        ..Default::default()
                    };
                }
                return ModelClashCheckResult {
                    clash_free: true,
                    ..Default::default()
                };
            } else if reapply_queue_present {
                return ModelClashCheckResult {
                    unknown: true,
                    ..Default::default()
                };
            } else {
                return ModelClashCheckResult {
                    unknown: true,
                    ..Default::default()
                };
            }
        }

        let concept_ref = concepts.get(concept);
        let op_code = concept_ref.get_operator_code();
        let op_count = concept_ref.get_operand_count();
        let concept_operator = concept_ref.get_concept_operator();

        if (negated && op_code == CCAND) || (!negated && (op_code == CCOR || op_code == CCEQ)) {
            let mut all_clash_found = true;
            let mut one_clash_free_found = false;
            let mut one_unknown_found = false;
            for operand_linker in concept_ref.get_operand_list() {
                if one_clash_free_found {
                    break;
                }
                let result = self.check_can_have_clash_with_model(
                    indi_node,
                    operand_linker.target,
                    operand_linker.negated ^ negated,
                    depth + 1,
                    tested_individuals_set,
                    indi_node,
                    concepts,
                    process_context,
                );
                one_clash_free_found |= result.clash_free;
                one_unknown_found |= result.unknown;
                all_clash_found &= result.clash_found;
            }
            if one_clash_free_found {
                ModelClashCheckResult {
                    clash_free: true,
                    ..Default::default()
                }
            } else if all_clash_found {
                ModelClashCheckResult {
                    clash_found: true,
                    ..Default::default()
                }
            } else {
                let _ = one_unknown_found;
                ModelClashCheckResult {
                    unknown: true,
                    ..Default::default()
                }
            }
        } else if op_count == 1 && (op_code == CCOR || op_code == CCEQ || op_code == CCAND) {
            if let Some(operand_linker) = concept_ref.get_operand_list().first() {
                self.check_can_have_clash_with_model(
                    indi_node,
                    operand_linker.target,
                    operand_linker.negated ^ negated,
                    depth + 1,
                    tested_individuals_set,
                    indi_node,
                    concepts,
                    process_context,
                )
            } else {
                ModelClashCheckResult {
                    unknown: true,
                    ..Default::default()
                }
            }
        } else if negated
            && (op_code == CCSUB || concept_operator.has_partial_operator_code_flag(CCFS_TRIG_TYPE))
        {
            ModelClashCheckResult {
                clash_free: true,
                ..Default::default()
            }
        } else if op_code == CCAQCHOOCE {
            let mut all_clash_found = true;
            let mut one_clash_free_found = false;
            let mut one_unknown_found = false;
            for operand_linker in concept_ref.get_operand_list() {
                if one_clash_free_found {
                    break;
                }
                let op_con_negation = operand_linker.negated;
                if op_con_negation == negated {
                    let result = self.check_can_have_clash_with_model(
                        indi_node,
                        operand_linker.target,
                        op_con_negation,
                        depth + 1,
                        tested_individuals_set,
                        indi_node,
                        concepts,
                        process_context,
                    );
                    one_clash_free_found |= result.clash_free;
                    one_unknown_found |= result.unknown;
                    all_clash_found &= result.clash_found;
                }
            }
            if one_clash_free_found {
                ModelClashCheckResult {
                    clash_free: true,
                    ..Default::default()
                }
            } else if all_clash_found {
                ModelClashCheckResult {
                    clash_found: true,
                    ..Default::default()
                }
            } else {
                let _ = one_unknown_found;
                ModelClashCheckResult {
                    unknown: true,
                    ..Default::default()
                }
            }
        } else if (negated && op_code == CCSOME)
            || (!negated && concept_operator.has_partial_operator_code_flag(CCFS_ALL_AQALL_TYPE))
        {
            let role = concept_ref.get_role();
            let role_succ_hash =
                process_context.node_reapply_role_successor_hash_existing(indi_node);
            if role_succ_hash.is_none() {
                return ModelClashCheckResult {
                    clash_free: true,
                    ..Default::default()
                };
            }
            let mut role_succ_it = process_context
                .role_succ_hash(role_succ_hash)
                .get_role_successor_link_iterator(process_context.edges(), role);
            if !role_succ_it.has_next() {
                return ModelClashCheckResult {
                    clash_free: true,
                    ..Default::default()
                };
            }

            let mut one_clash_found = false;
            let mut all_clash_free_found = true;
            let mut one_unknown_found = false;
            while !one_clash_found && role_succ_it.has_next() {
                let link = role_succ_it.next(true);
                if let Some(succ_indi_node) =
                    Self::successor_node_for_link(process_context, indi_node, link)
                {
                    for operand_linker in concept_ref.get_operand_list() {
                        if one_clash_found {
                            break;
                        }
                        let result = self.check_can_have_clash_with_model(
                            succ_indi_node,
                            operand_linker.target,
                            operand_linker.negated ^ negated,
                            depth + 1,
                            tested_individuals_set,
                            indi_node,
                            concepts,
                            process_context,
                        );
                        all_clash_free_found &= result.clash_free;
                        one_unknown_found |= result.unknown;
                        one_clash_found |= result.clash_found;
                    }
                } else {
                    one_unknown_found = true;
                    all_clash_free_found = false;
                }
            }

            if one_clash_found {
                ModelClashCheckResult {
                    clash_free: true,
                    ..Default::default()
                }
            } else if all_clash_free_found {
                ModelClashCheckResult {
                    clash_found: true,
                    ..Default::default()
                }
            } else {
                let _ = one_unknown_found;
                ModelClashCheckResult {
                    unknown: true,
                    ..Default::default()
                }
            }
        } else {
            ModelClashCheckResult {
                unknown: true,
                ..Default::default()
            }
        }
    }

    /// Port of `testEquivalenceConceptAlternatives(...)`.
    pub fn test_equivalence_concept_alternatives(
        &self,
        indi_node: NodeId,
        alternatives_set: &[(ConceptId, bool)],
        test_saturated_merged_hash: &mut std::collections::HashMap<
            (ConceptId, bool),
            SaturatedMergedTestItem,
        >,
        one_merge_satisfiable_flag: &mut bool,
        all_merge_unsatisfiable_flag: &mut bool,
        concepts: &Arena<Concept>,
        roles: &Arena<Role>,
        concept_process_datas: &Arena<ConceptProcessData>,
        concept_reference_linking_datas: &Arena<ConceptSaturationReferenceLinkingData>,
        saturation_concept_reference_linkings: &Arena<SaturationConceptReferenceLinking>,
        process_context: &mut ProcessContext,
        ontology_top_concept: Option<ConceptId>,
    ) -> bool {
        for (concept, negation) in alternatives_set.iter().copied() {
            let mut merged_satisfiable_flag = false;
            let merged_successfully_flag = self
                .test_subsumer_candidate_possible_with_merged_saturated_model(
                    indi_node,
                    concept,
                    negation,
                    &mut merged_satisfiable_flag,
                    concepts,
                    roles,
                    concept_process_datas,
                    concept_reference_linking_datas,
                    saturation_concept_reference_linkings,
                    process_context,
                    ontology_top_concept,
                );
            let saturated_merged_test_item = test_saturated_merged_hash
                .entry((concept, negation))
                .or_default();
            saturated_merged_test_item.successfully_merged = merged_successfully_flag;
            saturated_merged_test_item.satisfiable_merged = merged_satisfiable_flag;
            if !merged_successfully_flag {
                *all_merge_unsatisfiable_flag = false;
            } else if merged_satisfiable_flag {
                *one_merge_satisfiable_flag = true;
                *all_merge_unsatisfiable_flag = false;
                return true;
            }
        }

        if *all_merge_unsatisfiable_flag {
            return true;
        }
        false
    }

    /// Bounded port of the root pseudomodel message allocation/wrap section in
    /// `CSatisfiableTaskClassificationMessageAnalyser::analyseSatisfiableTask`.
    ///
    /// The full C++ method first traverses the completion graph and fills these
    /// concept/role entries. This helper ports the producer-side payload step:
    /// check `EFEXTRACTIDENTIFIERPSEUDOMODEL`, allocate model id `0`, set the
    /// valid concept/role maps, populate the maps, and return the
    /// `CClassificationPseudoModelIdentifierMessageData` equivalent.
    pub fn create_root_pseudo_model_identifier_message(
        &self,
        adapter: &SatisfiableTaskClassificationMessageAdapter,
        root_concepts: &[(ConceptId, bool)],
        root_roles: &[(RoleId, ClassificationClassPseudoModelRoleData)],
        memory_pools: Cint64,
    ) -> Option<ClassificationPseudoModelIdentifierMessageData> {
        if !adapter.has_extraction_flags(EFEXTRACTIDENTIFIERPSEUDOMODEL) {
            return None;
        }

        let testing_concept = adapter.get_testing_concept();
        if testing_concept.is_none() {
            return None;
        }

        let mut pm_model_hash = ClassificationClassPseudoModelHash::new();
        {
            let pm_model = pm_model_hash
                .get_pseudo_model_data_mut(0, true)
                .expect("created root pseudo-model data");
            pm_model.set_valid_concept_map(true);
            pm_model.set_valid_role_map(true);

            let con_map = pm_model
                .get_pseudo_model_concept_map_mut(true)
                .expect("created root pseudo-model concept map");
            for (concept, deterministic) in root_concepts {
                con_map.insert(
                    *concept,
                    ClassificationClassPseudoModelConceptData::new_with_deterministic(
                        *deterministic,
                    ),
                );
            }

            let role_map = pm_model
                .get_pseudo_model_role_map_mut(true)
                .expect("created root pseudo-model role map");
            for (role, role_data) in root_roles {
                role_map.insert(*role, role_data.clone());
            }
        }

        let mut pm_message_data = ClassificationPseudoModelIdentifierMessageData::new();
        pm_message_data.init_classification_pseudo_model_identifier_message_data(
            testing_concept,
            pm_model_hash,
            memory_pools,
        );
        Some(pm_message_data)
    }

    /// Bounded port of root-node class subsumer extraction in
    /// `CSatisfiableTaskClassificationMessageAnalyser::analyseSatisfiableTask`.
    ///
    /// C++ creates a `CClassificationClassSubsumptionMessageData` for the
    /// testing concept whenever the root-node subsumer extraction branch runs,
    /// even when the collected subsumer list is null.
    pub fn create_root_class_subsumption_message(
        &self,
        adapter: &SatisfiableTaskClassificationMessageAdapter,
        labels: &[ClassificationAnalyserConceptLabel],
        max_deterministic_branch_tag: Cint64,
        concepts: &Arena<Concept>,
    ) -> Option<ClassificationClassSubsumptionMessageData> {
        if !adapter.has_extraction_flags(EFEXTRACTSUBSUMERSROOTNODE) {
            return None;
        }
        let testing_concept = adapter.get_testing_concept();
        if testing_concept.is_none() {
            return None;
        }

        let mut subsumers = Vec::new();
        for label in Self::sorted_labels_by_concept_tag(labels, concepts) {
            if label.negated
                || label.concept == testing_concept
                || !Self::is_named_class(label.concept, concepts)
                || Self::concept_tag(label.concept, concepts) == 1
            {
                continue;
            }
            let deterministic = label
                .branching_tag
                .map(|branch_tag| branch_tag <= max_deterministic_branch_tag)
                .unwrap_or(false);
            if deterministic {
                subsumers.push(label.concept);
            }
        }

        let mut message = ClassificationClassSubsumptionMessageData::new();
        message.init_classification_subsumption_message_data(
            testing_concept,
            (!subsumers.is_empty()).then_some(subsumers),
        );
        Some(message)
    }

    pub fn create_root_class_subsumption_message_linker(
        &self,
        adapter: &SatisfiableTaskClassificationMessageAdapter,
        labels: &[ClassificationAnalyserConceptLabel],
        max_deterministic_branch_tag: Cint64,
        concepts: &Arena<Concept>,
    ) -> Option<ClassificationMessageDataLinker> {
        self.create_root_class_subsumption_message(
            adapter,
            labels,
            max_deterministic_branch_tag,
            concepts,
        )
        .map(|message| {
            ClassificationMessageDataLinker::from_message(
                ClassificationMessageDataPayload::from_class_subsumption(message),
            )
        })
    }

    /// Bounded port of the other-node class subsumer extraction block in
    /// `CSatisfiableTaskClassificationMessageAnalyser::analyseSatisfiableTask`.
    ///
    /// The caller supplies the already selected `analyseConcept`,
    /// `analyseBranchTag`, and whether the analysed descriptor is the
    /// single-dependency descriptor. This preserves the C++ branch-local
    /// collection semantics without porting the whole successor BFS yet.
    pub fn create_other_node_class_subsumption_message(
        &self,
        adapter: &SatisfiableTaskClassificationMessageAdapter,
        analyse_concept: ConceptId,
        analyse_branch_tag: Cint64,
        is_single_dependency_descriptor: bool,
        labels: &[ClassificationAnalyserConceptLabel],
        concepts: &Arena<Concept>,
    ) -> Option<ClassificationClassSubsumptionMessageData> {
        if !adapter.has_extraction_flags(EFEXTRACTSUBSUMERSOTHERNODES)
            || !is_single_dependency_descriptor
            || analyse_concept.is_none()
            || !Self::is_named_class(analyse_concept, concepts)
            || Self::concept_tag(analyse_concept, concepts) == 1
        {
            return None;
        }

        let mut subsumers = Vec::new();
        for label in Self::sorted_labels_by_concept_tag(labels, concepts) {
            if !Self::is_named_class(label.concept, concepts) {
                continue;
            }
            let Some(branch_tag) = label.branching_tag else {
                continue;
            };
            if branch_tag < analyse_branch_tag {
                return None;
            }
            if branch_tag == analyse_branch_tag
                && !label.negated
                && label.concept != analyse_concept
                && Self::concept_tag(label.concept, concepts) != 1
            {
                subsumers.push(label.concept);
            }
        }

        if subsumers.is_empty() {
            return None;
        }
        let mut message = ClassificationClassSubsumptionMessageData::new();
        message.init_classification_subsumption_message_data(analyse_concept, Some(subsumers));
        Some(message)
    }

    pub fn create_other_node_class_subsumption_message_linker(
        &self,
        adapter: &SatisfiableTaskClassificationMessageAdapter,
        analyse_concept: ConceptId,
        analyse_branch_tag: Cint64,
        is_single_dependency_descriptor: bool,
        labels: &[ClassificationAnalyserConceptLabel],
        concepts: &Arena<Concept>,
    ) -> Option<ClassificationMessageDataLinker> {
        self.create_other_node_class_subsumption_message(
            adapter,
            analyse_concept,
            analyse_branch_tag,
            is_single_dependency_descriptor,
            labels,
            concepts,
        )
        .map(|message| {
            ClassificationMessageDataLinker::from_message(
                ClassificationMessageDataPayload::from_class_subsumption(message),
            )
        })
    }

    /// Port of the analyser's `considerOtherNode` extraction guard.
    pub fn should_consider_other_nodes(
        adapter: &SatisfiableTaskClassificationMessageAdapter,
    ) -> bool {
        adapter.has_extraction_flags(
            EFEXTRACTSUBSUMERSOTHERNODES | EFEXTRACTPOSSIBLESUBSUMERSOTHERNODES,
        )
    }

    /// Port of the other-node BFS node guard before concept-label analysis.
    ///
    /// Konclude skips nominal nodes and nodes carrying
    /// `PRFINVALIDATEBLOCKERFLAGSCOMPINATION` before selecting either a
    /// multiple-dependency or single-dependency concept descriptor for
    /// classifier message extraction.
    pub fn is_other_node_analysis_allowed(
        is_nominal_individual_node: bool,
        has_invalidate_blocker_flags: bool,
    ) -> bool {
        !is_nominal_individual_node && !has_invalidate_blocker_flags
    }

    /// Bounded port of the other-node successor BFS in
    /// `CSatisfiableTaskClassificationMessageAnalyser::analyseSatisfiableTask`.
    ///
    /// The caller supplies node snapshots instead of live `CIndividualProcessNode`
    /// objects. The helper preserves Konclude's queue/processed-set behaviour,
    /// node skip guard, multiple-vs-single-dependency descriptor selection, and
    /// the fact that successor expansion only happens after a node passes the
    /// nominal/blocker guard.
    pub fn collect_other_node_analyse_visits(
        &self,
        adapter: &SatisfiableTaskClassificationMessageAdapter,
        base_individual_id: Cint64,
        initial_successor_individual_ids: &[Cint64],
        node_snapshots: &[ClassificationAnalyserOtherNodeSnapshot],
    ) -> Vec<ClassificationAnalyserOtherNodeVisit> {
        if !Self::should_consider_other_nodes(adapter) {
            return Vec::new();
        }

        let snapshot_by_id: std::collections::HashMap<_, _> = node_snapshots
            .iter()
            .map(|snapshot| (snapshot.individual_id, snapshot))
            .collect();
        let mut processed_individuals = std::collections::HashSet::new();
        let mut queue = std::collections::VecDeque::new();
        let mut visits = Vec::new();

        processed_individuals.insert(base_individual_id);
        for succ_id in initial_successor_individual_ids {
            if processed_individuals.insert(*succ_id) {
                queue.push_back(*succ_id);
            }
        }

        while let Some(individual_id) = queue.pop_front() {
            let Some(snapshot) = snapshot_by_id.get(&individual_id) else {
                continue;
            };
            if !Self::is_other_node_analysis_allowed(
                snapshot.is_nominal_individual_node,
                snapshot.has_invalidate_blocker_flags,
            ) {
                continue;
            }

            visits.extend(self.collect_other_node_snapshot_analyse_visits(adapter, snapshot));

            for succ_id in &snapshot.successor_individual_ids {
                if processed_individuals.insert(*succ_id) {
                    queue.push_back(*succ_id);
                }
            }
        }

        visits
    }

    /// Live graph variant of the other-node BFS pre-pass in
    /// `analyseSatisfiableTask`.
    ///
    /// Konclude seeds the queue from `baseIndi->getSuccessorIterator()`, tracks
    /// processed individual ids in `succIndiProcHash`, snapshots each reached
    /// process node, and only appends the node's own successors after the
    /// nominal/blocker guard succeeds.
    pub fn collect_live_other_node_snapshots_from_root(
        &self,
        process_context: &ProcessContext,
        ontology: &OntologyArenas,
        base_node: NodeId,
    ) -> (Vec<Cint64>, Vec<ClassificationAnalyserOtherNodeSnapshot>) {
        if base_node.is_none() || base_node.index() >= process_context.node_count() {
            return (Vec::new(), Vec::new());
        }

        let base_individual_id = process_context.node(base_node).individual_node_id();
        let mut processed_individuals = std::collections::HashSet::new();
        let mut queue = std::collections::VecDeque::new();
        let mut root_successor_individual_ids = Vec::new();
        let mut snapshots = Vec::new();

        processed_individuals.insert(base_individual_id);
        let mut root_succ_it = process_context.node_successor_iterator(base_node);
        while root_succ_it.has_next() {
            let succ_link = root_succ_it.next_link(true);
            if let Some(succ_node) =
                Self::successor_node_for_link(process_context, base_node, succ_link)
            {
                let succ_individual_id = process_context.node(succ_node).individual_node_id();
                if processed_individuals.insert(succ_individual_id) {
                    root_successor_individual_ids.push(succ_individual_id);
                    queue.push_back(succ_node);
                }
            }
        }

        while let Some(node) = queue.pop_front() {
            let Some(snapshot) = self
                .extract_other_node_snapshot_from_process_node_resolving_single_dependency(
                    process_context,
                    ontology,
                    node,
                )
            else {
                continue;
            };
            let expand_successors = Self::is_other_node_analysis_allowed(
                snapshot.is_nominal_individual_node,
                snapshot.has_invalidate_blocker_flags,
            );
            snapshots.push(snapshot);
            if !expand_successors {
                continue;
            }

            let mut succ_it = process_context.node_successor_iterator(node);
            while succ_it.has_next() {
                let succ_link = succ_it.next_link(true);
                if let Some(succ_node) =
                    Self::successor_node_for_link(process_context, node, succ_link)
                {
                    let succ_individual_id = process_context.node(succ_node).individual_node_id();
                    if processed_individuals.insert(succ_individual_id) {
                        queue.push_back(succ_node);
                    }
                }
            }
        }

        (root_successor_individual_ids, snapshots)
    }

    /// Collect the classifier-reference-backed "more information required" set
    /// for analysed other-node concepts.
    ///
    /// This ports the analyser-side gate that first resolves the analysed
    /// concept's classifier reference linking data and then asks the
    /// corresponding `COptimizedKPSetClassTestingItem` whether more
    /// classification information is still required.
    pub fn collect_other_node_concepts_requiring_more_information(
        &self,
        adapter: &SatisfiableTaskClassificationMessageAdapter,
        visits: &[ClassificationAnalyserOtherNodeVisit],
        concepts: &Arena<Concept>,
        concept_process_datas: &Arena<ConceptProcessData>,
        concept_reference_linking_datas: &Arena<ConceptSaturationReferenceLinkingData>,
        testing_items: &[OptimizedKPSetClassTestingItem],
    ) -> std::collections::HashSet<ConceptId> {
        let mut concepts_requiring_more_information = std::collections::HashSet::new();
        for visit in visits {
            if is_more_classification_information_required_for_concept(
                visit.label.concept,
                concepts,
                concept_process_datas,
                concept_reference_linking_datas,
                adapter,
                testing_items,
            ) {
                concepts_requiring_more_information.insert(visit.label.concept);
            }
        }
        concepts_requiring_more_information
    }

    fn collect_other_node_snapshot_analyse_visits(
        &self,
        adapter: &SatisfiableTaskClassificationMessageAdapter,
        snapshot: &ClassificationAnalyserOtherNodeSnapshot,
    ) -> Vec<ClassificationAnalyserOtherNodeVisit> {
        let extract_other_nodes_multiple_dependency =
            adapter.has_extraction_flags(EFEXTRACTOTHERNODESMULTIPLEDEPENDENCY);
        let extract_other_nodes_single_dependency =
            adapter.has_extraction_flags(EFEXTRACTOTHERNODESSINGLEDEPENDENCY);

        let mut analyse_label_index = None;
        let mut multiple_label_index = 0usize;
        if extract_other_nodes_multiple_dependency && !snapshot.labels.is_empty() {
            analyse_label_index = Some(0);
            multiple_label_index = 1;
        }

        let mut single_dependency_label_index = None;
        if (multiple_label_index < snapshot.labels.len() || extract_other_nodes_single_dependency)
            && !snapshot.has_successor_nominal_connection
        {
            single_dependency_label_index = snapshot
                .single_dependency_label_index
                .filter(|index| *index < snapshot.labels.len());
        }
        if analyse_label_index.is_none() {
            analyse_label_index = single_dependency_label_index;
        }
        if single_dependency_label_index.is_none() {
            analyse_label_index =
                (multiple_label_index < snapshot.labels.len()).then_some(multiple_label_index);
        }

        let mut visits = Vec::new();
        while let Some(label_index) = analyse_label_index {
            if let Some(label) = snapshot.labels.get(label_index).copied() {
                visits.push(ClassificationAnalyserOtherNodeVisit {
                    individual_id: snapshot.individual_id,
                    label,
                    is_single_dependency_descriptor: single_dependency_label_index
                        == Some(label_index),
                });
            }

            if extract_other_nodes_multiple_dependency {
                if Some(label_index) == Some(multiple_label_index) {
                    multiple_label_index += 1;
                }
                analyse_label_index =
                    (multiple_label_index < snapshot.labels.len()).then_some(multiple_label_index);
                if multiple_label_index < snapshot.labels.len() {
                    multiple_label_index += 1;
                }
            } else {
                analyse_label_index = None;
            }
        }

        visits
    }

    /// Extract the bounded W230 snapshot for a live process node.
    ///
    /// This ports the mechanical data collection around
    /// `indiNode->getReapplyConceptLabelSet(false)` and
    /// `indiNode->getSuccessorIterator()`. The single-ancestor dependency
    /// descriptor is still supplied explicitly until
    /// `getIndividualProcessNodeConceptWithSingleAncestorDependency(...)` is
    /// ported.
    pub fn extract_other_node_snapshot_from_process_node(
        &self,
        process_context: &ProcessContext,
        node: NodeId,
        single_dependency_label_index: Option<usize>,
    ) -> Option<ClassificationAnalyserOtherNodeSnapshot> {
        if node.is_none() {
            return None;
        }
        let node_ref = process_context.node(node);
        let label_set = node_ref.use_reapply_con_label_set;
        let labels =
            self.extract_classification_analyser_labels_from_label_set(process_context, label_set);

        let mut successor_individual_ids = Vec::new();
        let mut succ_it = process_context.node_successor_iterator(node);
        while succ_it.has_next() {
            let succ_indi_id = succ_it.next_individual_id(true);
            if succ_indi_id != 0 {
                successor_individual_ids.push(succ_indi_id);
            }
        }

        Some(ClassificationAnalyserOtherNodeSnapshot {
            individual_id: node_ref.individual_node_id(),
            is_nominal_individual_node: node_ref.is_nominal_individual_node(),
            has_invalidate_blocker_flags: node_ref.has_partial_processing_restriction_flags(
                IndividualProcessNode::PRF_INVALIDATEBLOCKERFLAGSCOMPINATION,
            ),
            has_successor_nominal_connection: node_ref.has_partial_processing_restriction_flags(
                IndividualProcessNode::PRF_SUCCESSORNOMINALCONNECTION,
            ),
            labels,
            single_dependency_label_index,
            successor_individual_ids,
        })
    }

    /// Live wrapper around W232 snapshot extraction that ports Konclude's
    /// `getIndividualProcessNodeConceptWithSingleAncestorDependency(...)`
    /// descriptor selection before building the snapshot.
    pub fn extract_other_node_snapshot_from_process_node_resolving_single_dependency(
        &self,
        process_context: &ProcessContext,
        ontology: &OntologyArenas,
        node: NodeId,
    ) -> Option<ClassificationAnalyserOtherNodeSnapshot> {
        let single_dependency_label_index = self
            .single_ancestor_dependency_label_index_from_process_node(
                process_context,
                ontology,
                node,
            );
        self.extract_other_node_snapshot_from_process_node(
            process_context,
            node,
            single_dependency_label_index,
        )
    }

    /// Port of
    /// `CSatisfiableTaskClassificationMessageAnalyser::getIndividualProcessNodeConceptWithSingleAncestorDependency`.
    pub fn individual_process_node_concept_with_single_ancestor_dependency(
        &self,
        process_context: &ProcessContext,
        ontology: &OntologyArenas,
        node: NodeId,
    ) -> Option<ConDescId> {
        self.single_ancestor_dependency_descriptor_and_index_from_process_node(
            process_context,
            ontology,
            node,
        )
        .map(|(con_des, _)| con_des)
    }

    pub fn single_ancestor_dependency_label_index_from_process_node(
        &self,
        process_context: &ProcessContext,
        ontology: &OntologyArenas,
        node: NodeId,
    ) -> Option<usize> {
        let (descriptor, _) = self
            .single_ancestor_dependency_descriptor_and_index_from_process_node(
                process_context,
                ontology,
                node,
            )?;
        let descriptor_ref = process_context.con_desc(descriptor);
        let target_concept = descriptor_ref.get_concept();
        let target_negated = descriptor_ref.is_negated();
        let label_set = process_context.node(node).use_reapply_con_label_set;
        self.extract_classification_analyser_labels_from_label_set(process_context, label_set)
            .iter()
            .position(|label| label.concept == target_concept && label.negated == target_negated)
    }

    fn single_ancestor_dependency_descriptor_and_index_from_process_node(
        &self,
        process_context: &ProcessContext,
        ontology: &OntologyArenas,
        node: NodeId,
    ) -> Option<(ConDescId, usize)> {
        if node.is_none()
            || process_context
                .node(node)
                .has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_SUCCESSORNOMINALCONNECTION,
                )
        {
            return None;
        }

        let label_set = process_context.node(node).use_reapply_con_label_set;
        if label_set.is_none() {
            return None;
        }

        let mut single_ancestor_dependency_concept = None;
        let mut con_des = process_context
            .label_set(label_set)
            .get_adding_sorted_concept_description_linker();
        let mut label_index = 0;
        while con_des.is_some() {
            let con_des_ref = process_context.con_desc(con_des);
            let next_con_des = con_des_ref.get_next_concept_descriptor();
            if con_des_ref.get_concept_tag(ontology) != 1 {
                let dep_track_point = con_des_ref.get_dependency_track_point();
                if dep_track_point.is_none() {
                    return None;
                }
                if self.has_dependency_to_ancestor(process_context, node, dep_track_point) {
                    if single_ancestor_dependency_concept.is_some() {
                        return None;
                    }
                    single_ancestor_dependency_concept = Some((con_des, label_index));
                }
                label_index += 1;
            }
            con_des = next_con_des;
        }

        single_ancestor_dependency_concept
    }

    /// Port of
    /// `CSatisfiableTaskClassificationMessageAnalyser::hasDependencyToAncestor`.
    pub fn has_dependency_to_ancestor(
        &self,
        process_context: &ProcessContext,
        individual_node: NodeId,
        dep_track_point: TrackPointId,
    ) -> bool {
        if individual_node.is_none() || dep_track_point.is_none() {
            return false;
        }

        let ancestor_depth = process_context
            .node(individual_node)
            .individual_ancestor_depth();
        if ancestor_depth <= 0 {
            let dep_node = process_context
                .track_point(dep_track_point)
                .dependency_node();
            return dep_node.is_some()
                && process_context
                    .dep_node(dep_node)
                    .is_independent_base_dependency_type();
        }

        let dep_node = process_context
            .track_point(dep_track_point)
            .dependency_node();
        if dep_node.is_none() {
            return false;
        }

        let dep_node_ref = process_context.dep_node(dep_node);
        let appropriate_individual = dep_node_ref.individual_node();
        if appropriate_individual.is_some() {
            return process_context
                .node(appropriate_individual)
                .individual_ancestor_depth()
                < ancestor_depth;
        }

        if dep_node_ref.kind() == DepKind::MergedConcept {
            return self.has_dependency_to_ancestor(
                process_context,
                individual_node,
                dep_node_ref.previous_dependency_track_point(),
            );
        }

        false
    }

    fn extract_classification_analyser_labels_from_label_set(
        &self,
        process_context: &ProcessContext,
        label_set: LabelSetId,
    ) -> Vec<ClassificationAnalyserConceptLabel> {
        if label_set.is_none() {
            return Vec::new();
        }
        let mut labels = Vec::new();
        let mut con_set_it =
            process_context.label_set_concept_label_set_iterator(label_set, true, true, false);
        while con_set_it.has_next() {
            let con_des = con_set_it.get_concept_descriptor();
            if con_des.is_some() {
                let con_des_ref = process_context.con_desc(con_des);
                let dep_track_point = con_set_it.get_dependency_track_point(process_context);
                let branching_tag = dep_track_point.is_some().then(|| {
                    process_context
                        .track_point(dep_track_point)
                        .get_branching_tag()
                });
                labels.push(ClassificationAnalyserConceptLabel::new(
                    con_des_ref.get_concept(),
                    con_des_ref.is_negated(),
                    branching_tag,
                ));
            }
            con_set_it.move_next(process_context);
        }
        labels
    }

    /// Bounded port of the analysed-concept scheduling block in
    /// `CSatisfiableTaskClassificationMessageAnalyser::analyseSatisfiableTask`.
    ///
    /// The caller has already resolved Konclude's
    /// `CClassificationSatisfiableCalculationConceptReferenceLinking` and passes
    /// whether it reports `isMoreConceptClassificationInformationRequired()`.
    /// Accepted concepts are inserted into `analysed_concepts`, preserving the
    /// C++ `analysedConceptSet` duplicate guard.
    pub fn select_other_node_analyse_candidate(
        &self,
        testing_concept: ConceptId,
        label: ClassificationAnalyserConceptLabel,
        more_concept_classification_information_required: bool,
        analysed_concepts: &mut std::collections::HashSet<ConceptId>,
        concepts: &Arena<Concept>,
    ) -> Option<ClassificationAnalyserOtherNodeCandidate> {
        if label.concept == testing_concept
            || Self::concept_tag(label.concept, concepts) == 1
            || label.negated
            || !Self::is_named_class(label.concept, concepts)
            || !more_concept_classification_information_required
        {
            return None;
        }

        let analyse_branch_tag = label.branching_tag?;
        if !analysed_concepts.insert(label.concept) {
            return None;
        }

        Some(ClassificationAnalyserOtherNodeCandidate {
            analyse_concept: label.concept,
            analyse_branch_tag,
        })
    }

    /// Bounded port of the message-production body after an other-node analysed
    /// descriptor has passed scheduling.
    ///
    /// C++ keeps class-subsumption and possible-subsumption linkers separate and
    /// prepends every newly produced message to the corresponding head. This
    /// helper preserves that shape over snapshot visits; final concatenation
    /// remains the job of `merge_classification_message_data_linkers`.
    pub fn create_other_node_classification_message_linkers(
        &self,
        adapter: &SatisfiableTaskClassificationMessageAdapter,
        testing_concept: ConceptId,
        visits: &[ClassificationAnalyserOtherNodeVisit],
        node_snapshots: &[ClassificationAnalyserOtherNodeSnapshot],
        concepts_requiring_more_information: &std::collections::HashSet<ConceptId>,
        analysed_concepts: &mut std::collections::HashSet<ConceptId>,
        possible_subsumption_states: &std::collections::HashMap<
            ConceptId,
            ClassificationAnalyserPossibleSubsumptionState,
        >,
        equivalent_non_candidate_concepts: &std::collections::HashMap<ConceptId, Vec<ConceptId>>,
        concepts: &Arena<Concept>,
    ) -> (
        Option<ClassificationMessageDataLinker>,
        Option<ClassificationMessageDataLinker>,
    ) {
        let snapshot_by_id: std::collections::HashMap<_, _> = node_snapshots
            .iter()
            .map(|snapshot| (snapshot.individual_id, snapshot))
            .collect();
        let mut subsum_message_data_linker: Option<ClassificationMessageDataLinker> = None;
        let mut poss_subsum_message_data_linker: Option<ClassificationMessageDataLinker> = None;

        for visit in visits {
            let Some(candidate) = self.select_other_node_analyse_candidate(
                testing_concept,
                visit.label,
                concepts_requiring_more_information.contains(&visit.label.concept),
                analysed_concepts,
                concepts,
            ) else {
                continue;
            };
            let Some(snapshot) = snapshot_by_id.get(&visit.individual_id) else {
                continue;
            };

            if let Some(class_linker) = self.create_other_node_class_subsumption_message_linker(
                adapter,
                candidate.analyse_concept,
                candidate.analyse_branch_tag,
                visit.is_single_dependency_descriptor,
                &snapshot.labels,
                concepts,
            ) {
                subsum_message_data_linker =
                    Some(if let Some(existing_linker) = subsum_message_data_linker {
                        class_linker.append_linker(existing_linker)
                    } else {
                        class_linker
                    });
            }

            let default_state = ClassificationAnalyserPossibleSubsumptionState::uninitialized();
            let state = possible_subsumption_states
                .get(&candidate.analyse_concept)
                .unwrap_or(&default_state);
            let equivalent_non_candidates = equivalent_non_candidate_concepts
                .get(&candidate.analyse_concept)
                .map(Vec::as_slice)
                .unwrap_or(&[]);
            if let Some(poss_payload) = self
                .create_possible_class_subsumption_message_with_extraction_flag(
                    adapter,
                    EFEXTRACTPOSSIBLESUBSUMERSOTHERNODES,
                    candidate.analyse_concept,
                    &snapshot.labels,
                    state,
                    !equivalent_non_candidates.is_empty(),
                    (!equivalent_non_candidates.is_empty())
                        .then_some(equivalent_non_candidates.to_vec()),
                    None,
                    None,
                    concepts,
                )
            {
                let poss_linker = ClassificationMessageDataLinker::from_message(poss_payload);
                poss_subsum_message_data_linker = Some(
                    if let Some(existing_linker) = poss_subsum_message_data_linker {
                        poss_linker.append_linker(existing_linker)
                    } else {
                        poss_linker
                    },
                );
            }
        }

        (subsum_message_data_linker, poss_subsum_message_data_linker)
    }

    pub fn create_other_node_classification_message_linkers_with_live_equivalent_non_candidates(
        &self,
        adapter: &SatisfiableTaskClassificationMessageAdapter,
        testing_concept: ConceptId,
        visits: &[ClassificationAnalyserOtherNodeVisit],
        node_snapshots: &[ClassificationAnalyserOtherNodeSnapshot],
        concepts_requiring_more_information: &std::collections::HashSet<ConceptId>,
        analysed_concepts: &mut std::collections::HashSet<ConceptId>,
        possible_subsumption_states: &std::collections::HashMap<
            ConceptId,
            ClassificationAnalyserPossibleSubsumptionState,
        >,
        process_context: &mut ProcessContext,
        ontology: &OntologyArenas,
        individual_node_vector: &IndividualProcessNodeVector,
        concepts: &Arena<Concept>,
        roles: &Arena<Role>,
        concept_process_datas: &Arena<ConceptProcessData>,
        concept_reference_linking_datas: &Arena<ConceptSaturationReferenceLinkingData>,
        saturation_concept_reference_linkings: &Arena<SaturationConceptReferenceLinking>,
        ontology_top_concept: Option<ConceptId>,
    ) -> (
        Option<ClassificationMessageDataLinker>,
        Option<ClassificationMessageDataLinker>,
    ) {
        let snapshot_by_id: std::collections::HashMap<_, _> = node_snapshots
            .iter()
            .map(|snapshot| (snapshot.individual_id, snapshot))
            .collect();
        let mut subsum_message_data_linker: Option<ClassificationMessageDataLinker> = None;
        let mut poss_subsum_message_data_linker: Option<ClassificationMessageDataLinker> = None;

        for visit in visits {
            let Some(candidate) = self.select_other_node_analyse_candidate(
                testing_concept,
                visit.label,
                concepts_requiring_more_information.contains(&visit.label.concept),
                analysed_concepts,
                concepts,
            ) else {
                continue;
            };
            let Some(snapshot) = snapshot_by_id.get(&visit.individual_id) else {
                continue;
            };

            if let Some(class_linker) = self.create_other_node_class_subsumption_message_linker(
                adapter,
                candidate.analyse_concept,
                candidate.analyse_branch_tag,
                visit.is_single_dependency_descriptor,
                &snapshot.labels,
                concepts,
            ) {
                subsum_message_data_linker =
                    Some(if let Some(existing_linker) = subsum_message_data_linker {
                        class_linker.append_linker(existing_linker)
                    } else {
                        class_linker
                    });
            }

            let default_state = ClassificationAnalyserPossibleSubsumptionState::uninitialized();
            let state = possible_subsumption_states
                .get(&candidate.analyse_concept)
                .unwrap_or(&default_state);
            let snapshot_node = individual_node_vector.get_data(snapshot.individual_id);
            if snapshot_node.is_none() {
                continue;
            }
            if let Some(poss_payload) = self
                .create_possible_class_subsumption_message_with_live_equivalent_non_candidates(
                    adapter,
                    candidate.analyse_concept,
                    &snapshot.labels,
                    state,
                    snapshot_node,
                    ontology,
                    concepts,
                    roles,
                    concept_process_datas,
                    concept_reference_linking_datas,
                    saturation_concept_reference_linkings,
                    process_context,
                    ontology_top_concept,
                )
            {
                let poss_linker = ClassificationMessageDataLinker::from_message(poss_payload);
                poss_subsum_message_data_linker = Some(
                    if let Some(existing_linker) = poss_subsum_message_data_linker {
                        poss_linker.append_linker(existing_linker)
                    } else {
                        poss_linker
                    },
                );
            }
        }

        (subsum_message_data_linker, poss_subsum_message_data_linker)
    }

    /// Bounded port of
    /// `CSatisfiableTaskClassificationMessageAnalyser::extractPossibleSubsumptionInformation`.
    pub fn create_possible_class_subsumption_message(
        &self,
        adapter: &SatisfiableTaskClassificationMessageAdapter,
        testing_concept: ConceptId,
        labels: &[ClassificationAnalyserConceptLabel],
        state: &ClassificationAnalyserPossibleSubsumptionState,
        equivalent_non_candidate_concepts: &[ConceptId],
        concepts: &Arena<Concept>,
    ) -> Option<ClassificationMessageDataPayload> {
        self.create_possible_class_subsumption_message_with_extraction_flag(
            adapter,
            EFEXTRACTPOSSIBLESUBSUMERSROOTNODE,
            testing_concept,
            labels,
            state,
            !equivalent_non_candidate_concepts.is_empty(),
            (!equivalent_non_candidate_concepts.is_empty())
                .then_some(equivalent_non_candidate_concepts.to_vec()),
            None,
            None,
            concepts,
        )
    }

    pub fn create_possible_class_subsumption_message_with_live_equivalent_non_candidates(
        &self,
        adapter: &SatisfiableTaskClassificationMessageAdapter,
        testing_concept: ConceptId,
        labels: &[ClassificationAnalyserConceptLabel],
        state: &ClassificationAnalyserPossibleSubsumptionState,
        indi_node: NodeId,
        ontology: &OntologyArenas,
        concepts: &Arena<Concept>,
        roles: &Arena<Role>,
        concept_process_datas: &Arena<ConceptProcessData>,
        concept_reference_linking_datas: &Arena<ConceptSaturationReferenceLinkingData>,
        saturation_concept_reference_linkings: &Arena<SaturationConceptReferenceLinking>,
        process_context: &mut ProcessContext,
        ontology_top_concept: Option<ConceptId>,
    ) -> Option<ClassificationMessageDataPayload> {
        let (eq_concepts_non_candidate_possible_subsumers, possible_subsumers) = self
            .collect_equivalent_non_candidate_possible_subsumers(
                indi_node,
                ontology,
                concepts,
                roles,
                concept_process_datas,
                concept_reference_linking_datas,
                saturation_concept_reference_linkings,
                process_context,
                ontology_top_concept,
            );
        self.create_possible_class_subsumption_message_with_equivalent_non_candidates(
            adapter,
            testing_concept,
            labels,
            state,
            eq_concepts_non_candidate_possible_subsumers,
            &possible_subsumers,
            None,
            None,
            concepts,
        )
    }

    fn create_possible_class_subsumption_message_with_equivalent_non_candidates(
        &self,
        adapter: &SatisfiableTaskClassificationMessageAdapter,
        testing_concept: ConceptId,
        labels: &[ClassificationAnalyserConceptLabel],
        state: &ClassificationAnalyserPossibleSubsumptionState,
        has_equivalent_non_candidates: bool,
        possible_subsumers: &[ConceptId],
        possible_subsumer_template: Option<
            &[(ClassificationInitializePossibleClassSubsumptionData, Option<ConceptId>)],
        >,
        label_tags: Option<&std::collections::HashSet<Cint64>>,
        concepts: &Arena<Concept>,
    ) -> Option<ClassificationMessageDataPayload> {
        // Only initialization messages consume the owned candidate list.
        // Update messages retain the same boolean flag but need no clone.
        let possible_subsumers = (!state.possible_subsumption_map_initialized
            && !possible_subsumers.is_empty())
        .then(|| possible_subsumers.to_vec());
        self.create_possible_class_subsumption_message_with_extraction_flag(
            adapter,
            EFEXTRACTPOSSIBLESUBSUMERSROOTNODE,
            testing_concept,
            labels,
            state,
            has_equivalent_non_candidates,
            possible_subsumers,
            possible_subsumer_template,
            label_tags,
            concepts,
        )
    }

    fn possible_subsumer_message_template(
        labels: &[ClassificationAnalyserConceptLabel],
        concepts: &Arena<Concept>,
    ) -> Vec<(ClassificationInitializePossibleClassSubsumptionData, Option<ConceptId>)> {
        let mut template = Vec::new();
        for label in Self::sorted_labels_by_concept_tag(labels, concepts) {
            if !label.negated
                && Self::is_named_class(label.concept, concepts)
                && Self::concept_tag(label.concept, concepts) != 1
            {
                template.push((
                    ClassificationInitializePossibleClassSubsumptionData::new(label.concept),
                    Some(label.concept),
                ));
            }
            if Self::operator_code(label.concept, concepts) == CCEQCAND
                && label.eq_candidate_possible_with_merged_saturated_model
            {
                template.push((
                    ClassificationInitializePossibleClassSubsumptionData::new(label.concept),
                    None,
                ));
            }
        }
        template
    }

    fn create_possible_class_subsumption_message_with_extraction_flag(
        &self,
        adapter: &SatisfiableTaskClassificationMessageAdapter,
        extraction_flag: Cint64,
        testing_concept: ConceptId,
        labels: &[ClassificationAnalyserConceptLabel],
        state: &ClassificationAnalyserPossibleSubsumptionState,
        eq_concepts_non_candidate_possible_subsumers: bool,
        eq_concept_non_candidate_possible_subsumer_list: Option<Vec<ConceptId>>,
        possible_subsumer_template: Option<
            &[(ClassificationInitializePossibleClassSubsumptionData, Option<ConceptId>)],
        >,
        cached_label_tags: Option<&std::collections::HashSet<Cint64>>,
        concepts: &Arena<Concept>,
    ) -> Option<ClassificationMessageDataPayload> {
        if !adapter.has_extraction_flags(extraction_flag) || testing_concept.is_none() {
            return None;
        }

        if !state.possible_subsumption_map_initialized {
            let possible_subsumer_list = if let Some(template) = possible_subsumer_template {
                template
                    .iter()
                    .filter(|(_, excluded_for)| *excluded_for != Some(testing_concept))
                    .map(|(candidate, _)| candidate.clone())
                    .collect()
            } else {
                let mut possible_subsumer_list = Vec::new();
                for label in Self::sorted_labels_by_concept_tag(labels, concepts) {
                    if !label.negated
                        && Self::is_named_class(label.concept, concepts)
                        && Self::concept_tag(label.concept, concepts) != 1
                        && label.concept != testing_concept
                    {
                        possible_subsumer_list.push(
                            ClassificationInitializePossibleClassSubsumptionData::new(
                                label.concept,
                            ),
                        );
                    }
                    if Self::operator_code(label.concept, concepts) == CCEQCAND
                        && label.eq_candidate_possible_with_merged_saturated_model
                    {
                        possible_subsumer_list.push(
                            ClassificationInitializePossibleClassSubsumptionData::new(
                                label.concept,
                            ),
                        );
                    }
                }
                possible_subsumer_list
            };

            let mut message = ClassificationInitializePossibleClassSubsumptionMessageData::new();
            message.init_classification_possible_subsumption_message_data(
                testing_concept,
                (!possible_subsumer_list.is_empty()).then_some(possible_subsumer_list),
                eq_concepts_non_candidate_possible_subsumers,
                eq_concept_non_candidate_possible_subsumer_list,
            );
            return Some(
                ClassificationMessageDataPayload::from_initialize_possible_class_subsumption(
                    message,
                ),
            );
        }

        if !state.remaining_possible_subsumptions {
            return None;
        }

        let owned_label_tags;
        let label_tags = if let Some(label_tags) = cached_label_tags {
            label_tags
        } else {
            owned_label_tags = labels
                .iter()
                .map(|label| Self::concept_tag(label.concept, concepts))
                .collect();
            &owned_label_tags
        };
        let updated_possible_subsumptions =
            state
                .possible_subsumption_concepts
                .iter()
                .any(|poss_concept| {
                    !label_tags.contains(&Self::concept_tag(*poss_concept, concepts))
                        && Self::operator_code(*poss_concept, concepts) != CCEQ
                });
        if updated_possible_subsumptions {
            let mut message = ClassificationUpdatePossibleClassSubsumptionMessageData::new();
            message.init_classification_possible_subsumption_message_data(testing_concept);
            Some(ClassificationMessageDataPayload::from_update_possible_class_subsumption(message))
        } else {
            None
        }
    }

    pub fn create_possible_class_subsumption_message_linker(
        &self,
        adapter: &SatisfiableTaskClassificationMessageAdapter,
        testing_concept: ConceptId,
        labels: &[ClassificationAnalyserConceptLabel],
        state: &ClassificationAnalyserPossibleSubsumptionState,
        equivalent_non_candidate_concepts: &[ConceptId],
        concepts: &Arena<Concept>,
    ) -> Option<ClassificationMessageDataLinker> {
        self.create_possible_class_subsumption_message(
            adapter,
            testing_concept,
            labels,
            state,
            equivalent_non_candidate_concepts,
            concepts,
        )
        .map(ClassificationMessageDataLinker::from_message)
    }

    /// Port of the duplicate-init-list pruning branch in
    /// `extractPossibleSubsumptionInformation`.
    ///
    /// When `mMultiplePossSubsumInitAvoidHash` already contains a possible
    /// subsumer list for the testing concept, C++ walks the current sorted label
    /// set and the existing possible-subsumer list by concept tag. Existing
    /// possible subsumers missing from the current label set are marked invalid,
    /// and no new classification message is allocated in this branch.
    pub fn prune_reused_possible_subsumption_init_list(
        &self,
        labels: &[ClassificationAnalyserConceptLabel],
        possible_subsumer_list: &mut [ClassificationInitializePossibleClassSubsumptionData],
        concepts: &Arena<Concept>,
    ) -> bool {
        let sorted_labels = Self::sorted_labels_by_concept_tag(labels, concepts);
        let mut label_index = 0;
        let mut poss_index = 0;
        let mut invalidated_any = false;

        while label_index < sorted_labels.len() && poss_index < possible_subsumer_list.len() {
            let label_tag = Self::concept_tag(sorted_labels[label_index].concept, concepts);
            let poss_tag = Self::concept_tag(
                possible_subsumer_list[poss_index].get_possible_subsumer_concept(),
                concepts,
            );

            if label_tag < poss_tag {
                label_index += 1;
            } else if label_tag == poss_tag {
                label_index += 1;
                poss_index += 1;
            } else {
                invalidated_any |= possible_subsumer_list[poss_index].is_possible_subsumer_valid();
                possible_subsumer_list[poss_index].set_possible_subsumer_invalid();
                poss_index += 1;
            }
        }

        while poss_index < possible_subsumer_list.len() {
            invalidated_any |= possible_subsumer_list[poss_index].is_possible_subsumer_valid();
            possible_subsumer_list[poss_index].set_possible_subsumer_invalid();
            poss_index += 1;
        }

        invalidated_any
    }

    /// Port of the bounded pseudomodel producer loop in
    /// `CSatisfiableTaskClassificationMessageAnalyser::analyseSatisfiableTask`.
    ///
    /// This owns the C++ `pmModelHash` construction: seed model `0` with the
    /// base individual, pop `CPseudoModelAnalyseProcessItem`s, set concept/role
    /// validity, fill maps via the ported W215/W217 helpers, queue successor
    /// process items, and finally wrap the hash in a pseudomodel identifier
    /// message.
    pub fn create_pseudo_model_identifier_message_from_base_node(
        &self,
        adapter: &SatisfiableTaskClassificationMessageAdapter,
        process_context: &ProcessContext,
        base_node: NodeId,
        nondeterministically_merged: bool,
        max_deterministic_branch_tag: Cint64,
        concepts: &Arena<Concept>,
        roles: &Arena<Role>,
        memory_pools: Cint64,
    ) -> Option<ClassificationPseudoModelIdentifierMessageData> {
        if !adapter.has_extraction_flags(EFEXTRACTIDENTIFIERPSEUDOMODEL) {
            return None;
        }

        let testing_concept = adapter.get_testing_concept();
        if testing_concept.is_none() || base_node.is_none() || nondeterministically_merged {
            return None;
        }

        let mut pm_model_hash = ClassificationClassPseudoModelHash::new();
        let mut next_model_id = 1;
        let mut current_pseudo_model_nodes_count = 0;
        let mut process_items = Vec::new();
        let mut base_process_item =
            PseudoModelAnalyseProcessItem::init_pseudo_model_analyse_process_item(0, 0);
        base_process_item.add_node(base_node, false);
        process_items.push(base_process_item);

        while let Some(process_item) = process_items.pop() {
            current_pseudo_model_nodes_count += 1;
            let (valid_concepts, valid_successors) = self.evaluate_pseudo_model_map_validity(
                process_context,
                &process_item.nodes,
                process_item.root_distance,
                current_pseudo_model_nodes_count,
            );

            let pm_model = pm_model_hash
                .get_pseudo_model_data_mut(process_item.pseudo_model_id, true)
                .expect("created pseudo-model data");
            pm_model.set_valid_concept_map(valid_concepts);
            pm_model.set_valid_role_map(valid_successors);

            if valid_concepts {
                let con_map = pm_model
                    .get_pseudo_model_concept_map_mut(true)
                    .expect("created pseudo-model concept map");
                for (node, non_deterministic_connected) in &process_item.nodes {
                    if node.is_none() {
                        continue;
                    }
                    let label_set = process_context.node(*node).use_reapply_con_label_set;
                    for (concept, deterministic) in self
                        .extract_pseudo_model_concepts_from_label_set(
                            process_context,
                            label_set,
                            max_deterministic_branch_tag,
                            *non_deterministic_connected,
                            concepts,
                        )
                    {
                        con_map.insert(
                            concept,
                            ClassificationClassPseudoModelConceptData::new_with_deterministic(
                                deterministic,
                            ),
                        );
                    }
                }
            }

            if valid_successors {
                let (role_entries, queued_items) = self.extract_pseudo_model_role_successor_data(
                    process_context,
                    &process_item,
                    max_deterministic_branch_tag,
                    &mut next_model_id,
                    concepts,
                    roles,
                );
                let role_map = pm_model
                    .get_pseudo_model_role_map_mut(true)
                    .expect("created pseudo-model role map");
                for (role, role_data) in role_entries {
                    role_map.insert(role, role_data);
                }
                for queued_item in queued_items {
                    process_items.push(queued_item);
                }
            }
        }

        let mut pm_message_data = ClassificationPseudoModelIdentifierMessageData::new();
        pm_message_data.init_classification_pseudo_model_identifier_message_data(
            testing_concept,
            pm_model_hash,
            memory_pools,
        );
        Some(pm_message_data)
    }

    /// Port of `pmMessageDataLinker = pmMessageData->append(pmMessageDataLinker)`
    /// for the pseudomodel producer branch.
    pub fn create_pseudo_model_identifier_message_linker_from_base_node(
        &self,
        adapter: &SatisfiableTaskClassificationMessageAdapter,
        process_context: &ProcessContext,
        base_node: NodeId,
        nondeterministically_merged: bool,
        max_deterministic_branch_tag: Cint64,
        concepts: &Arena<Concept>,
        roles: &Arena<Role>,
        memory_pools: Cint64,
    ) -> Option<ClassificationMessageDataLinker> {
        self.create_pseudo_model_identifier_message_from_base_node(
            adapter,
            process_context,
            base_node,
            nondeterministically_merged,
            max_deterministic_branch_tag,
            concepts,
            roles,
            memory_pools,
        )
        .map(|message| {
            ClassificationMessageDataLinker::from_message(
                ClassificationMessageDataPayload::PseudoModelIdentifier(message),
            )
        })
    }

    /// Port of the final classification message linker concatenation in
    /// `CSatisfiableTaskClassificationMessageAnalyser::analyseSatisfiableTask`.
    ///
    /// C++ starts with the subsumption linker, prepends the pseudomodel linker,
    /// then prepends the possible-subsumption linker, yielding final traversal
    /// order: possible-subsumption, pseudomodel, subsumption.
    pub fn merge_classification_message_data_linkers(
        &self,
        subsum_message_data_linker: Option<ClassificationMessageDataLinker>,
        pm_message_data_linker: Option<ClassificationMessageDataLinker>,
        poss_subsum_message_data_linker: Option<ClassificationMessageDataLinker>,
    ) -> Option<ClassificationMessageDataLinker> {
        let mut message_data_linker = subsum_message_data_linker;
        if let Some(pm_message_data_linker) = pm_message_data_linker {
            message_data_linker = Some(if let Some(message_data_linker) = message_data_linker {
                pm_message_data_linker.append_linker(message_data_linker)
            } else {
                pm_message_data_linker
            });
        }
        if let Some(poss_subsum_message_data_linker) = poss_subsum_message_data_linker {
            message_data_linker = Some(if let Some(message_data_linker) = message_data_linker {
                poss_subsum_message_data_linker.append_linker(message_data_linker)
            } else {
                poss_subsum_message_data_linker
            });
        }
        message_data_linker.filter(|message_data_linker| !message_data_linker.is_empty())
    }

    /// Port of the final message-output tail in
    /// `CSatisfiableTaskClassificationMessageAnalyser::analyseSatisfiableTask`.
    ///
    /// C++ first concatenates `subsumMessageDataLinker`,
    /// `pmMessageDataLinker`, and `possSubsumMessageDataLinker` in that order
    /// with each later family prepended as the new head. If the resulting chain
    /// is non-null it calls `tellClassificationMessage`; otherwise it releases
    /// the temporary memory pools. The Rust port records the release branch as an
    /// opaque memory-pool handle until the task memory manager is live.
    pub fn deliver_merged_classification_message_data<O: ClassificationMessageDataObserver>(
        &self,
        adapter: &SatisfiableTaskClassificationMessageAdapter,
        subsum_message_data_linker: Option<ClassificationMessageDataLinker>,
        pm_message_data_linker: Option<ClassificationMessageDataLinker>,
        poss_subsum_message_data_linker: Option<ClassificationMessageDataLinker>,
        memory_pool: Cint64,
        observer: Option<&mut O>,
    ) -> ClassificationAnalyserMessageOutputResult {
        let message_data_linker = self.merge_classification_message_data_linkers(
            subsum_message_data_linker,
            pm_message_data_linker,
            poss_subsum_message_data_linker,
        );
        if message_data_linker.is_some() {
            let delivered = deliver_classification_message_data_to_observer(
                adapter,
                message_data_linker,
                memory_pool,
                observer,
            );
            ClassificationAnalyserMessageOutputResult {
                had_message_data: true,
                delivered_to_observer: delivered,
                released_memory_pool: None,
            }
        } else {
            ClassificationAnalyserMessageOutputResult {
                had_message_data: false,
                delivered_to_observer: false,
                released_memory_pool: Some(memory_pool),
            }
        }
    }

    /// Port of the pseudomodel concept-map population loop over a
    /// `CReapplyConceptLabelSetIterator`.
    pub fn extract_pseudo_model_concepts_from_label_set(
        &self,
        process_context: &ProcessContext,
        label_set: LabelSetId,
        max_deterministic_branch_tag: Cint64,
        non_deterministic_connected: bool,
        concepts: &super::super::model::substrate::Arena<super::super::model::concept::Concept>,
    ) -> Vec<(ConceptId, bool)> {
        let mut extracted = Vec::new();
        if label_set.is_none() {
            return extracted;
        }

        let mut con_set_it =
            process_context.label_set_concept_label_set_iterator(label_set, true, true, false);
        while con_set_it.has_next() {
            let con_des = con_set_it.get_concept_descriptor();
            if con_des.is_some() {
                let con_des_ref = process_context.con_desc(con_des);
                let dep_track_point = con_set_it.get_dependency_track_point(process_context);
                let deterministic = dep_track_point.is_some()
                    && process_context
                        .track_point(dep_track_point)
                        .get_branching_tag()
                        <= max_deterministic_branch_tag
                    && !non_deterministic_connected;

                let concept = con_des_ref.get_concept();
                let concept_ref = concepts.get(concept);
                let con_op_code = concept_ref.get_operator_code();
                let insert_con = !con_des_ref.is_negated()
                    && ((concept_ref.has_class_name() && con_op_code == CCATOM)
                        || con_op_code == CCSUB
                        || con_op_code == CCIMPLTRIG
                        || con_op_code == CCEQCAND);
                if insert_con {
                    extracted.push((concept, deterministic));
                }
            }
            con_set_it.move_next(process_context);
        }
        extracted
    }

    /// Port of the pseudomodel concept/role map validity gate before map
    /// population in `analyseSatisfiableTask`.
    pub fn evaluate_pseudo_model_map_validity(
        &self,
        process_context: &ProcessContext,
        nodes: &[(NodeId, bool)],
        root_distance: Cint64,
        current_pseudo_model_nodes_count: Cint64,
    ) -> (bool, bool) {
        let mut valid_concepts = true;
        let mut valid_successors = true;

        for (node_id, _) in nodes {
            if node_id.is_none() {
                continue;
            }
            let node = process_context.node(*node_id);
            let completion_graph_cached_valid = node.has_partial_processing_restriction_flags(
                IndividualProcessNode::PRF_COMPLETIONGRAPHCACHED,
            ) && !node
                .has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_COMPLETIONGRAPHCACHINGINVALID
                        | IndividualProcessNode::PRF_COMPLETIONGRAPHCACHINGINVALIDATED,
                );
            let blocked_or_cached = node.has_partial_processing_restriction_flags(
                IndividualProcessNode::PRF_INVALIDATEBLOCKERFLAGSCOMPINATION
                    | IndividualProcessNode::PRF_SATURATIONBLOCKINGCACHED
                    | IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDSUCCESSOREXPANSIONBLOCKED,
            ) || completion_graph_cached_valid;
            if blocked_or_cached {
                valid_concepts = false;
                valid_successors = false;
            }
            if node.is_nominal_individual_node() {
                valid_successors = false;
            }
        }

        if root_distance > Self::MAX_PSEUDO_MODEL_DEPTH
            || current_pseudo_model_nodes_count > Self::MAX_PSEUDO_MODEL_NODES
        {
            valid_successors = false;
        }

        (valid_concepts, valid_successors)
    }

    /// Port of the pseudomodel role-successor map population block in
    /// `CSatisfiableTaskClassificationMessageAnalyser::analyseSatisfiableTask`.
    ///
    /// Returns the `pmModelRoleMap` entries and the queued successor
    /// `CPseudoModelAnalyseProcessItem` records. The caller owns `next_model_id`
    /// just like the C++ `nextModelID` local.
    pub fn extract_pseudo_model_role_successor_data(
        &self,
        process_context: &ProcessContext,
        process_item: &PseudoModelAnalyseProcessItem,
        max_deterministic_branch_tag: Cint64,
        next_model_id: &mut Cint64,
        concepts: &Arena<Concept>,
        roles: &Arena<Role>,
    ) -> (
        Vec<(RoleId, ClassificationClassPseudoModelRoleData)>,
        Vec<PseudoModelAnalyseProcessItem>,
    ) {
        let mut role_entries = Vec::new();
        let mut process_items = Vec::new();
        let mut processed_roles = std::collections::HashSet::new();

        for (node_id, non_deterministic_connected) in &process_item.nodes {
            if node_id.is_none() {
                continue;
            }
            let role_succ_hash =
                process_context.node_reapply_role_successor_hash_existing(*node_id);
            if role_succ_hash.is_none() {
                continue;
            }

            let mut role_it = process_context
                .role_succ_hash(role_succ_hash)
                .get_role_iterator();
            while role_it.has_next() {
                let role = role_it.next(true);
                if role.is_none()
                    || roles.get(role).is_complex_role()
                    || !processed_roles.insert(role)
                {
                    continue;
                }

                let mut lower_det_at_least_bound: Cint64 = 0;
                let mut upper_at_least_bound: Cint64 = 0;
                let mut upper_det_at_most_bound: Cint64 = Cint64::MAX;
                let mut lower_at_most_bound: Cint64 = Cint64::MAX;
                let mut has_deterministic_successor = false;
                let mut succ_nodes = Vec::new();
                let mut seen_successor_ids = std::collections::HashSet::new();

                for (succ_source_node, _) in &process_item.nodes {
                    if succ_source_node.is_none() {
                        continue;
                    }
                    let succ_hash = process_context
                        .node_reapply_role_successor_hash_existing(*succ_source_node);
                    if succ_hash.is_some() {
                        let mut link_count = 0;
                        let mut succ_link_it = process_context
                            .role_succ_hash_role_successor_link_iterator_count(
                                succ_hash,
                                role,
                                Some(&mut link_count),
                            );
                        upper_at_least_bound = upper_at_least_bound.max(link_count);
                        lower_at_most_bound = lower_at_most_bound.min(link_count);

                        while succ_link_it.has_next() {
                            let succ_link = succ_link_it.next(true);
                            if succ_link.is_none() {
                                continue;
                            }
                            if let Some(succ_node) = Self::successor_node_for_link(
                                process_context,
                                *succ_source_node,
                                succ_link,
                            ) {
                                let succ_indi_id =
                                    process_context.node(succ_node).individual_node_id();
                                if seen_successor_ids.insert(succ_indi_id) {
                                    let mut deterministic_link = !*non_deterministic_connected;
                                    let dep_track_point = process_context
                                        .edge(succ_link)
                                        .get_dependency_track_point();
                                    if dep_track_point.is_some()
                                        && process_context
                                            .track_point(dep_track_point)
                                            .get_branching_tag()
                                            <= max_deterministic_branch_tag
                                    {
                                        lower_det_at_least_bound = lower_det_at_least_bound.max(1);
                                        if !*non_deterministic_connected {
                                            has_deterministic_successor = true;
                                        }
                                        deterministic_link = false;
                                    }
                                    succ_nodes.push((succ_node, deterministic_link));
                                }
                            }
                        }
                    } else {
                        lower_at_most_bound = 0;
                    }

                    Self::update_pseudo_model_role_bounds_from_label_set(
                        process_context,
                        process_context
                            .node(*succ_source_node)
                            .use_reapply_con_label_set,
                        role,
                        max_deterministic_branch_tag,
                        concepts,
                        &mut lower_det_at_least_bound,
                        &mut upper_det_at_most_bound,
                    );
                }

                let succ_pm_model_id = *next_model_id;
                *next_model_id += 1;

                let mut role_data = ClassificationClassPseudoModelRoleData::new();
                role_data.set_successor_model_id(succ_pm_model_id);
                role_data.set_deterministic(has_deterministic_successor);
                role_data.set_lower_at_least_bound(lower_det_at_least_bound);
                role_data.set_upper_at_least_bound(upper_at_least_bound);
                role_data.set_upper_at_most_bound(upper_det_at_most_bound);
                role_data.set_lower_at_most_bound(lower_at_most_bound);
                role_entries.push((role, role_data));

                let mut succ_process_item =
                    PseudoModelAnalyseProcessItem::init_pseudo_model_analyse_process_item(
                        succ_pm_model_id,
                        process_item.root_distance + 1,
                    );
                succ_process_item.nodes = succ_nodes;
                process_items.push(succ_process_item);
            }
        }

        (role_entries, process_items)
    }

    fn successor_node_for_link(
        process_context: &ProcessContext,
        source_node: NodeId,
        link: EdgeId,
    ) -> Option<NodeId> {
        let edge = process_context.edge(link);
        if edge.get_source_individual() == source_node {
            Some(edge.get_destination_individual())
        } else if edge.get_destination_individual() == source_node {
            Some(edge.get_source_individual())
        } else {
            None
        }
    }

    fn label_set_contains_concept_resolved(
        process_context: &ProcessContext,
        concepts: &Arena<Concept>,
        label_set: LabelSetId,
        concept: ConceptId,
        negated: bool,
    ) -> bool {
        if label_set.is_none()
            || label_set.index() >= process_context.label_set_count()
            || concept.is_none()
            || concept.index() >= concepts.len()
        {
            return false;
        }
        let con_tag = Self::concept_tag(concept, concepts);
        let mut con_des = ConDescId::NONE;
        let mut dep_track_point = TrackPointId::NONE;
        if !process_context
            .label_set(label_set)
            .get_concept_descriptor_by_tag(con_tag, &mut con_des, &mut dep_track_point)
        {
            return false;
        }
        con_des.is_some()
            && con_des.index() < process_context.con_desc_count()
            && process_context.con_desc(con_des).is_negated() == negated
    }

    fn label_set_concept_negation_resolved(
        process_context: &ProcessContext,
        concepts: &Arena<Concept>,
        label_set: LabelSetId,
        concept: ConceptId,
    ) -> Option<bool> {
        if label_set.is_none()
            || label_set.index() >= process_context.label_set_count()
            || concept.is_none()
            || concept.index() >= concepts.len()
        {
            return None;
        }
        let con_tag = Self::concept_tag(concept, concepts);
        let mut con_des = ConDescId::NONE;
        let mut dep_track_point = TrackPointId::NONE;
        if !process_context
            .label_set(label_set)
            .get_concept_descriptor_by_tag(con_tag, &mut con_des, &mut dep_track_point)
        {
            return None;
        }
        if con_des.is_some() && con_des.index() < process_context.con_desc_count() {
            Some(process_context.con_desc(con_des).is_negated())
        } else {
            None
        }
    }

    fn label_set_concept_model_entry_resolved(
        process_context: &ProcessContext,
        concepts: &Arena<Concept>,
        label_set: LabelSetId,
        concept: ConceptId,
    ) -> Option<(ConDescId, bool, TrackPointId, bool)> {
        if label_set.is_none()
            || label_set.index() >= process_context.label_set_count()
            || concept.is_none()
            || concept.index() >= concepts.len()
        {
            return None;
        }
        let con_tag = Self::concept_tag(concept, concepts);
        let mut con_des = ConDescId::NONE;
        let mut dep_track_point = TrackPointId::NONE;
        let mut reapply_queue_present = false;
        let mut reapply_queue_empty = true;
        if !process_context
            .label_set(label_set)
            .get_concept_descriptor_or_reapply_queue_state_by_tag(
                con_tag,
                &mut con_des,
                &mut dep_track_point,
                &mut reapply_queue_present,
                &mut reapply_queue_empty,
            )
        {
            return None;
        }
        let contains_negated = con_des.is_some()
            && con_des.index() < process_context.con_desc_count()
            && process_context.con_desc(con_des).is_negated();
        let dep_track_point =
            if con_des.is_some() && con_des.index() < process_context.con_desc_count() {
                process_context
                    .con_desc(con_des)
                    .get_dependency_track_point()
            } else {
                dep_track_point
            };
        let _ = reapply_queue_empty;
        Some((
            con_des,
            contains_negated,
            dep_track_point,
            reapply_queue_present,
        ))
    }

    fn sorted_labels_by_concept_tag(
        labels: &[ClassificationAnalyserConceptLabel],
        concepts: &Arena<Concept>,
    ) -> Vec<ClassificationAnalyserConceptLabel> {
        let mut sorted = labels.to_vec();
        sorted.sort_by_key(|label| Self::concept_tag(label.concept, concepts));
        sorted
    }

    fn concept_tag(concept: ConceptId, concepts: &Arena<Concept>) -> Cint64 {
        if concept.is_some() && concept.index() < concepts.len() {
            concepts.get(concept).get_concept_tag()
        } else {
            Cint64::MAX
        }
    }

    fn operator_code(concept: ConceptId, concepts: &Arena<Concept>) -> Cint64 {
        if concept.is_some() && concept.index() < concepts.len() {
            concepts.get(concept).get_operator_code()
        } else {
            Cint64::MAX
        }
    }

    fn is_named_class(concept: ConceptId, concepts: &Arena<Concept>) -> bool {
        concept.is_some()
            && concept.index() < concepts.len()
            && concepts.get(concept).has_class_name()
    }

    fn update_pseudo_model_role_bounds_from_label_set(
        process_context: &ProcessContext,
        label_set: LabelSetId,
        role: RoleId,
        max_deterministic_branch_tag: Cint64,
        concepts: &Arena<Concept>,
        lower_det_at_least_bound: &mut Cint64,
        upper_det_at_most_bound: &mut Cint64,
    ) {
        if label_set.is_none() {
            return;
        }

        let mut con_set_it =
            process_context.label_set_concept_label_set_iterator(label_set, true, true, false);
        while con_set_it.has_next() {
            let con_des = con_set_it.get_concept_descriptor();
            if con_des.is_some() {
                let con_des_ref = process_context.con_desc(con_des);
                let concept = concepts.get(con_des_ref.get_concept());
                let dep_track_point = con_set_it.get_dependency_track_point(process_context);
                if concept.get_role() == role
                    && dep_track_point.is_some()
                    && process_context
                        .track_point(dep_track_point)
                        .get_branching_tag()
                        <= max_deterministic_branch_tag
                {
                    let con_negation = con_des_ref.is_negated();
                    let op_code = concept.get_operator_code();
                    if (!con_negation && op_code == CCATLEAST)
                        || (con_negation && op_code == CCATMOST)
                    {
                        let at_least_param =
                            concept.get_parameter() + if con_negation { 1 } else { 0 };
                        if at_least_param >= 0 {
                            *lower_det_at_least_bound =
                                (*lower_det_at_least_bound).max(at_least_param);
                        }
                    }
                    if (con_negation && op_code == CCATLEAST)
                        || (!con_negation
                            && op_code == CCATMOST
                            && concept.get_operand_list().is_empty())
                    {
                        let at_most_param =
                            concept.get_parameter() - if con_negation { 1 } else { 0 };
                        if at_most_param >= 0 {
                            *upper_det_at_most_bound =
                                (*upper_det_at_most_bound).min(at_most_param);
                        }
                    }
                }
            }
            con_set_it.move_next(process_context);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::super::cache::sigexpand::{
        ExpanderCacheValueLinker, SigExpanderCacheEntryId, SignatureSatisfiableExpanderCacheEntry,
        SignatureSatisfiableExpanderCacheReader, SignatureSatisfiableExpanderCacheRedirectionItem,
        SignatureSatisfiableExpanderCacheSlotItem,
    };
    use super::super::super::cache::value::{CacheValue, CacheValueIdentifier};
    use super::super::super::classifier::ClassificationClassPseudoModelRoleData;
    use super::super::super::classifier::ClassificationMessageDataObserverRegistry;
    use super::super::super::classifier::OptimizedKPSetClassPossibleSubsumptionData;
    use super::super::super::classifier::RecordingClassificationMessageDataObserver;
    use super::super::super::completion::context::CalculationAlgorithmContext;
    use super::super::super::model::concept::Concept;
    use super::super::super::model::ontology::OntologyArenas;
    use super::super::super::model::op::{
        CCALL, CCAND, CCAQCHOOCE, CCATLEAST, CCATMOST, CCATOM, CCEQ, CCEQCAND, CCIMPLTRIG, CCSOME,
        CCSUB, CCTOP,
    };
    use super::super::super::model::role::Role;
    use super::super::super::model::stubs::NameId;
    use super::super::super::model::substrate::{Arena, NegLink};
    use super::super::super::model::{ConceptId, IndividualId, RoleId, INVALID};
    use super::super::super::process::context::ProcessContext;
    use super::super::super::process::databox::ProcessingDataBox;
    use super::super::super::process::dependency::{
        DepNodeBase, DependencyNode, DependencyTrackPoint,
    };
    use super::super::super::process::descriptor::ConceptDescriptor;
    use super::super::super::process::edge::IndividualLinkEdge;
    use super::super::super::process::node::{IndividualProcessNode, IndividualType};
    use super::super::super::process::reapply_sat::ReapplyConceptDescriptor;
    use super::super::super::process::rs1::ReapplyQueueIterator;
    use super::super::super::process::sat_node::IndividualSaturationProcessNode;
    use super::super::super::process::sat_ref::ExtendedConceptReferenceLinkingData;
    use super::super::super::process::satellites::{
        ConceptDescriptorDependencyReapplyData, CondensedReapplyQueue, ReapplyConceptLabelSet,
    };
    use super::super::super::process::stubs::ProcessContextId;
    use super::super::super::process::varbind::VarBindingPathId;
    use super::super::super::process::{DependencyId, NodeId, TrackPointId};
    use super::super::super::saturation::satellites::{
        BackwardSaturationPropagationReapplyDescriptor, ConceptSaturationDescriptor,
        ConceptSaturationDescriptorReapplyData, ReapplyConceptSaturationLabelSet,
        RoleBackwardSaturationPropagationHash, RoleBackwardSaturationPropagationHashData,
        SaturationSuccessorData,
    };
    use super::super::super::task::adapters::{
        SatisfiableTaskClassificationMessageAdapter, EFEXTRACTIDENTIFIERPSEUDOMODEL,
        EFEXTRACTOTHERNODESMULTIPLEDEPENDENCY, EFEXTRACTOTHERNODESSINGLEDEPENDENCY,
        EFEXTRACTPOSSIBLESUBSUMERSOTHERNODES, EFEXTRACTPOSSIBLESUBSUMERSROOTNODE,
        EFEXTRACTSUBSUMERSOTHERNODES, EFEXTRACTSUBSUMERSROOTNODE,
    };
    use super::*;
    use std::collections::HashMap;

    fn concept_with_tag(op_code: Cint64, tag: Cint64, named: bool) -> Concept {
        let mut concept = Concept::new();
        concept.set_operator_code(op_code).set_concept_tag(tag);
        if named {
            concept.add_class_name_linker(NameId::new(tag));
        }
        concept
    }

    fn dependency_base(
        kind: DepKind,
        individual_node: NodeId,
        previous_track_point: TrackPointId,
    ) -> DepNodeBase {
        DepNodeBase {
            process_tag: 0,
            concept_descriptor: ConDescId::NONE,
            individual_node,
            kind,
            dep_track_point: previous_track_point,
            additional_after: super::super::super::process::DepLinkId::NONE,
            selected_var_bind_path: VarBindingPathId::NONE,
            resolve_var_bind_path_map: None,
            resolve_rep_prop_map: None,
            base_assertion_role: RoleId::NONE,
            base_assertion_individual: IndividualId::NONE,
        }
    }

    fn add_ontology_label_descriptor(
        process_context: &mut ProcessContext,
        label_set: LabelSetId,
        ontology: &OntologyArenas,
        concept: ConceptId,
        negated: bool,
        track_point: TrackPointId,
    ) -> ConDescId {
        let previous_head = process_context
            .label_set(label_set)
            .get_adding_sorted_concept_description_linker();
        let mut con_des = ConceptDescriptor::new();
        con_des.concept = concept;
        con_des.negated = negated;
        con_des
            .set_dependency_track_point(track_point)
            .set_next(previous_head);
        let con_des_id = process_context.alloc_con_desc(con_des);
        let con_tag = ontology.concept(concept).get_concept_tag();
        let concept_identity = ontology.concept(concept) as *const _ as usize as Cint64;
        process_context
            .label_set_mut(label_set)
            .insert_concept_get_clash_resolved(
                con_des_id,
                concept,
                con_tag,
                negated,
                concept_identity,
                &|_stored| false,
                None,
                None,
            );
        con_des_id
    }

    fn add_dependency_track_point(
        process_context: &mut ProcessContext,
        kind: DepKind,
        individual_node: NodeId,
        previous_track_point: TrackPointId,
    ) -> TrackPointId {
        let dep_node = process_context.alloc_dep_node(DependencyNode::Deterministic {
            base: dependency_base(kind, individual_node, previous_track_point),
        });
        process_context.alloc_track_point(DependencyTrackPoint::new(dep_node))
    }

    fn add_branch_track_point(
        process_context: &mut ProcessContext,
        branching_tag: Cint64,
    ) -> TrackPointId {
        let mut dep_track_point = DependencyTrackPoint::new(DependencyId::NONE);
        dep_track_point.process_tag = branching_tag;
        process_context.alloc_track_point(dep_track_point)
    }

    fn add_label_descriptor(
        process_context: &mut ProcessContext,
        label_set: LabelSetId,
        concepts: &Arena<Concept>,
        concept: ConceptId,
        negated: bool,
        track_point: TrackPointId,
    ) {
        let previous_head = process_context
            .label_set(label_set)
            .get_adding_sorted_concept_description_linker();
        let mut con_des = ConceptDescriptor::new();
        con_des.concept = concept;
        con_des.negated = negated;
        con_des
            .set_dependency_track_point(track_point)
            .set_next(previous_head);
        let con_des_id = process_context.alloc_con_desc(con_des);
        let con_tag = concepts.get(concept).get_concept_tag();
        let concept_identity = concepts.get(concept) as *const _ as usize as Cint64;
        process_context
            .label_set_mut(label_set)
            .insert_concept_get_clash_resolved(
                con_des_id,
                concept,
                con_tag,
                negated,
                concept_identity,
                &|_stored| false,
                None,
                None,
            );
    }

    fn add_completion_label_set_node(process_context: &mut ProcessContext) -> (NodeId, LabelSetId) {
        let mut label_set = ReapplyConceptLabelSet::new(INVALID);
        label_set.init_concept_label_set(None);
        let label_set = process_context.alloc_label_set(label_set);
        let mut node = IndividualProcessNode::new(ProcessContextId::NONE);
        node.set_reapply_concept_label_set(label_set);
        let node = process_context.alloc_node(node);
        (node, label_set)
    }

    fn seed_sat_expander_handler_entry(
        handler: &mut SatisfiableExpanderCacheHandler,
        signature: Cint64,
        concept: ConceptId,
        concept_tag: Cint64,
        negated: bool,
        satisfiable: bool,
        expander_count: Cint64,
    ) -> SigExpanderCacheEntryId {
        let mut linker = ExpanderCacheValueLinker::new();
        let identifier = if negated {
            CacheValueIdentifier::CacheValTagAndNegatedConcept
        } else {
            CacheValueIdentifier::CacheValTagAndConcept
        };
        linker.set_cache_value(CacheValue::new_value(
            concept_tag,
            concept.index() as Cint64,
            identifier,
        ));
        let linker = handler
            .cache_context
            .alloc_expander_cache_value_linker(linker);

        let mut entry = SignatureSatisfiableExpanderCacheEntry::new();
        entry.det_expand_value_linker = linker;
        entry.det_expand_count = expander_count;
        entry.set_satisfiable(satisfiable);
        let entry = handler.cache_context.alloc_sig_expander_cache_entry(entry);

        let mut redirection = SignatureSatisfiableExpanderCacheRedirectionItem::new();
        redirection.init_redirection_item(entry, signature, expander_count);
        let redirection = handler
            .cache_context
            .alloc_sig_expander_redirection_item(redirection);

        let mut slot = SignatureSatisfiableExpanderCacheSlotItem::new();
        let mut sig_hash = HashMap::new();
        sig_hash.insert(signature, redirection);
        slot.set_signature_item_hash(sig_hash);
        slot.inc_reader();
        let slot = handler.cache_context.alloc_sig_expander_slot_item(slot);

        let mut reader = SignatureSatisfiableExpanderCacheReader::new();
        reader.current_slot = slot;
        let reader = handler
            .cache_context
            .alloc_sig_expander_cache_reader(reader);
        handler.sat_cache_reader = reader;
        entry
    }

    #[test]
    fn satisfiable_expander_handler_reads_signature_cache_hit() {
        let mut process_context = ProcessContext::new();
        let mut concepts = Arena::new();
        let concept = concepts.push(concept_with_tag(CCATOM, 101, true));
        let (node, label_set) = add_completion_label_set_node(&mut process_context);
        add_label_descriptor(
            &mut process_context,
            label_set,
            &concepts,
            concept,
            false,
            TrackPointId::NONE,
        );
        let signature = process_context
            .label_set(label_set)
            .get_concept_signature_value();

        let mut handler = SatisfiableExpanderCacheHandler::new();
        let seeded_entry =
            seed_sat_expander_handler_entry(&mut handler, signature, concept, 101, false, true, 1);
        let mut satisfiable = false;
        let mut entry = SigExpanderCacheEntryId::NONE;

        assert!(handler.is_individual_node_expand_cached(
            &process_context,
            node,
            Some(&mut satisfiable),
            Some(&mut entry),
        ));
        assert!(satisfiable);
        assert_eq!(entry, seeded_entry);
    }

    #[test]
    fn satisfiable_expander_handler_rejects_smaller_expander_count() {
        let mut process_context = ProcessContext::new();
        let mut concepts = Arena::new();
        let concept = concepts.push(concept_with_tag(CCATOM, 102, true));
        let (node, label_set) = add_completion_label_set_node(&mut process_context);
        add_label_descriptor(
            &mut process_context,
            label_set,
            &concepts,
            concept,
            false,
            TrackPointId::NONE,
        );
        let signature = process_context
            .label_set(label_set)
            .get_concept_signature_value();

        let mut handler = SatisfiableExpanderCacheHandler::new();
        seed_sat_expander_handler_entry(&mut handler, signature, concept, 102, false, true, 0);

        assert!(!handler.is_individual_node_expand_cached(&process_context, node, None, None));
    }

    #[test]
    fn satisfiable_expander_handler_rejects_negation_mismatch() {
        let mut process_context = ProcessContext::new();
        let mut concepts = Arena::new();
        let concept = concepts.push(concept_with_tag(CCATOM, 103, true));
        let (node, label_set) = add_completion_label_set_node(&mut process_context);
        add_label_descriptor(
            &mut process_context,
            label_set,
            &concepts,
            concept,
            false,
            TrackPointId::NONE,
        );
        let signature = process_context
            .label_set(label_set)
            .get_concept_signature_value();

        let mut handler = SatisfiableExpanderCacheHandler::new();
        seed_sat_expander_handler_entry(&mut handler, signature, concept, 103, true, true, 1);

        assert!(!handler.is_individual_node_expand_cached(&process_context, node, None, None));
    }

    #[test]
    fn satisfiable_expander_handler_extends_an_earlier_signature_with_cached_suffix() {
        let mut process_context = ProcessContext::new();
        let mut ontology = OntologyArenas::new();
        // Keep the synthetic base concept off arena index zero. With one
        // descriptor whose tag is 201, the faithful signature fold would be
        // `201 ^ 201 ^ 0 == 0`; zero is the cache protocol's "no previous
        // signature" sentinel and is not representative of ontology labels.
        ontology.alloc_concept(concept_with_tag(CCATOM, 200, true));
        let base_concept = ontology.alloc_concept(concept_with_tag(CCATOM, 201, true));
        let derived_concept = ontology.alloc_concept(concept_with_tag(CCATOM, 202, true));
        let (node, label_set) = add_completion_label_set_node(&mut process_context);
        let base_descriptor = add_ontology_label_descriptor(
            &mut process_context,
            label_set,
            &ontology,
            base_concept,
            false,
            TrackPointId::NONE,
        );
        let base_signature = process_context
            .label_set(label_set)
            .get_concept_signature_value();

        let mut handler = SatisfiableExpanderCacheHandler::new();
        assert!(handler.cache_individual_node_expansion(&mut process_context, &ontology, node,));
        assert!(handler.write_data.is_none());

        let mut dependency = dependency_base(DepKind::And, node, TrackPointId::NONE);
        dependency.concept_descriptor = base_descriptor;
        let dependency =
            process_context.alloc_dep_node(DependencyNode::Deterministic { base: dependency });
        let dependency = process_context.alloc_track_point(DependencyTrackPoint::new(dependency));
        add_ontology_label_descriptor(
            &mut process_context,
            label_set,
            &ontology,
            derived_concept,
            false,
            dependency,
        );
        let derived_signature = process_context
            .label_set(label_set)
            .get_concept_signature_value();
        assert_ne!(base_signature, derived_signature);

        // Konclude returns false after publishing the two transition writes;
        // the return value denotes an already reusable entry, not a write.
        assert!(!handler.cache_individual_node_expansion(&mut process_context, &ontology, node,));
        assert!(handler.write_data.is_some());
        assert!(handler.commit_cache_messages());
        assert_eq!(
            handler.cache_context.sig_expander_entry_write_datas.len(),
            0
        );
        assert_eq!(
            handler.cache_context.sig_expander_cache_value_lists.len(),
            0
        );
        assert_eq!(handler.cache_context.sig_expander_dep_hashes.len(), 0);

        let base_entry = handler.cache_entry_for_signature(base_signature);
        let derived_entry = handler.cache_entry_for_signature(derived_signature);
        assert!(base_entry.is_some());
        assert_eq!(base_entry, derived_entry);
        assert_eq!(
            handler
                .cache_context
                .sig_expander_cache_entry(base_entry)
                .get_expander_cache_value_count(),
            2
        );

        let first = handler
            .cache_context
            .sig_expander_cache_entry(base_entry)
            .get_expander_cache_value_linker();
        let second = handler
            .cache_context
            .expander_cache_value_linker(first)
            .get_next();
        assert_eq!(
            handler
                .cache_context
                .expander_cache_value_linker(first)
                .get_cache_value()
                .get_tag(),
            201
        );
        assert_eq!(
            handler
                .cache_context
                .expander_cache_value_linker(second)
                .get_cache_value()
                .get_tag(),
            202
        );
        assert_eq!(
            handler
                .cache_context
                .expander_cache_value_linker(second)
                .get_expander_dependency_list(),
            &vec![first]
        );
    }

    fn add_saturation_label_set_node(
        process_context: &mut ProcessContext,
    ) -> (
        SatNodeId,
        super::super::super::saturation::satellites::ReapplyConceptSaturationLabelSetId,
    ) {
        let mut label_set = ReapplyConceptSaturationLabelSet::new(INVALID);
        label_set.init_reapply_concept_saturation_label_set();
        let label_set = process_context.alloc_reapply_con_sat_label_set(label_set);
        let mut sat_node = IndividualSaturationProcessNode::new(11);
        sat_node.reapply_con_sat_label_set = label_set;
        sat_node.set_completed(true);
        let sat_node = process_context.alloc_sat_node(sat_node);
        (sat_node, label_set)
    }

    fn add_saturation_label_descriptor(
        process_context: &mut ProcessContext,
        label_set: super::super::super::saturation::satellites::ReapplyConceptSaturationLabelSetId,
        concepts: &Arena<Concept>,
        concept: ConceptId,
        negated: bool,
        imp_reapply: Cint64,
    ) -> super::super::super::saturation::satellites::ConceptSaturationDescriptorId {
        let mut con_sat_des = ConceptSaturationDescriptor::new();
        con_sat_des.init_concept_saturation_descriptor(concept, negated);
        let con_sat_des = process_context.alloc_con_sat_desc(con_sat_des);
        let con_tag = concepts.get(concept).get_concept_tag();
        process_context
            .reapply_con_sat_label_set_mut(label_set)
            .concept_des_dep_hash
            .insert(
                con_tag,
                ConceptSaturationDescriptorReapplyData {
                    con_sat_des,
                    imp_reapply_con_sat_des: super::super::super::saturation::satellites::ImplicationReapplyConceptSaturationDescriptorId::new(imp_reapply),
                },
            );
        con_sat_des
    }

    fn set_saturation_label_descriptor_linker(
        process_context: &mut ProcessContext,
        label_set: super::super::super::saturation::satellites::ReapplyConceptSaturationLabelSetId,
        descriptors: &[super::super::super::saturation::satellites::ConceptSaturationDescriptorId],
    ) {
        let head = descriptors.first().copied().unwrap_or(
            super::super::super::saturation::satellites::ConceptSaturationDescriptorId::NONE,
        );
        process_context
            .reapply_con_sat_label_set_mut(label_set)
            .concept_sat_des_linker = head;
        for pair in descriptors.windows(2) {
            process_context.con_sat_desc_mut(pair[0]).set_next(pair[1]);
        }
        if let Some(last) = descriptors.last().copied() {
            process_context.con_sat_desc_mut(last).set_next(
                super::super::super::saturation::satellites::ConceptSaturationDescriptorId::NONE,
            );
        }
    }

    fn add_linked_role_saturation_successor(
        process_context: &mut ProcessContext,
        source: SatNodeId,
        role: RoleId,
        successor: SatNodeId,
        active_count: Cint64,
        creation_roles: Vec<NegLink<RoleId>>,
    ) -> super::super::super::saturation::satellites::SaturationSuccessorDataId {
        process_context
            .sat_node_mut(source)
            .direct_status_flags
            .add_flags_code(IndividualSaturationProcessNodeStatusFlags::INDSUCCESSORNODEEXTENSIONS);
        let hash = process_context.sat_node_ext_linked_role_successor_hash(source, true);
        let role_data = process_context.linked_role_successor_data(hash, role, true);
        let mut succ_data = SaturationSuccessorData::new();
        succ_data
            .set_successor_individual_node(successor)
            .set_active_count(active_count);
        succ_data.creation_role_linker = creation_roles;
        let succ_data = process_context.alloc_sat_succ_data(succ_data);
        process_context
            .linked_role_sat_succ_data_mut(role_data)
            .succ_node_data_map
            .insert(successor.raw, succ_data);
        succ_data
    }

    fn add_saturation_concept_descriptor(
        process_context: &mut ProcessContext,
        concept: ConceptId,
        negated: bool,
    ) -> super::super::super::saturation::satellites::ConceptSaturationDescriptorId {
        let mut con_sat_des = ConceptSaturationDescriptor::new();
        con_sat_des.init_concept_saturation_descriptor(concept, negated);
        process_context.alloc_con_sat_desc(con_sat_des)
    }

    fn add_saturation_concept_reference(
        process_context: &mut ProcessContext,
        sat_node: super::super::super::process::SatNodeId,
        concept: ConceptId,
        negated: bool,
    ) {
        let mut ref_data = ExtendedConceptReferenceLinkingData::new();
        ref_data.init_concept_saturation_testing_item(concept, negated, RoleId::NONE);
        let ref_data = process_context.alloc_extended_con_ref_linking_data(ref_data);
        process_context
            .sat_node_mut(sat_node)
            .concept_saturation_link_ref_data = ref_data;
    }

    fn add_backward_reapply_for_role(
        process_context: &mut ProcessContext,
        sat_node: SatNodeId,
        role: RoleId,
        con_sat_des: super::super::super::saturation::satellites::ConceptSaturationDescriptorId,
    ) -> super::super::super::saturation::satellites::BackwardSaturationPropagationReapplyDescriptorId
    {
        let mut reapply = BackwardSaturationPropagationReapplyDescriptor::new();
        reapply.init_backward_propagation_reapply_descriptor(con_sat_des);
        let reapply = process_context.alloc_backward_sat_prop_reapply_desc(reapply);
        let hash = if process_context
            .sat_node(sat_node)
            .role_back_prop_hash
            .is_some()
        {
            process_context.sat_node(sat_node).role_back_prop_hash
        } else {
            let mut hash = RoleBackwardSaturationPropagationHash::new(INVALID);
            hash.init_role_backward_saturation_propagation_hash();
            let hash = process_context.alloc_role_backward_sat_prop_hash(hash);
            process_context.sat_node_mut(sat_node).role_back_prop_hash = hash;
            hash
        };
        process_context
            .role_backward_sat_prop_hash_mut(hash)
            .role_back_prop_data_hash
            .entry(role)
            .or_insert_with(RoleBackwardSaturationPropagationHashData::new)
            .reapply_linker = reapply;
        reapply
    }

    fn add_saturation_reference(
        saturation_reference_linkings: &mut Arena<SaturationConceptReferenceLinking>,
        sat_node: SatNodeId,
    ) -> Id<SaturationConceptReferenceLinking> {
        let mut linking = SaturationConceptReferenceLinking::new();
        linking.set_individual_process_node_for_concept(sat_node);
        saturation_reference_linkings.push(linking)
    }

    fn attach_concept_reference_data(
        concepts: &mut Arena<Concept>,
        concept: ConceptId,
        concept_process_datas: &mut Arena<ConceptProcessData>,
        concept_reference_linking_datas: &mut Arena<ConceptSaturationReferenceLinkingData>,
        data: ConceptSaturationReferenceLinkingData,
    ) {
        let con_ref = concept_reference_linking_datas.push(data);
        let mut con_proc = ConceptProcessData::new();
        con_proc.set_concept_reference_linking(con_ref);
        let con_proc = concept_process_datas.push(con_proc);
        concepts.get_mut(concept).set_concept_data(con_proc.raw);
    }

    fn add_node(process_context: &mut ProcessContext, flags: Cint64, nominal: bool) -> NodeId {
        let mut node = IndividualProcessNode::new(ProcessContextId::NONE);
        node.processing_restriction_flags = flags;
        if nominal {
            node.set_individual_type(IndividualType::Nominal);
        }
        process_context.alloc_node(node)
    }

    fn add_identified_node(process_context: &mut ProcessContext, indi_id: Cint64) -> NodeId {
        let mut node = IndividualProcessNode::new(ProcessContextId::NONE);
        node.set_individual_node_id(indi_id);
        process_context.alloc_node(node)
    }

    fn add_role_link(
        process_context: &mut ProcessContext,
        source: NodeId,
        destination: NodeId,
        role: RoleId,
        track_point: TrackPointId,
    ) {
        let mut edge = IndividualLinkEdge::new();
        edge.init_individual_link_edge(source, source, destination, role, track_point);
        let edge_id = process_context.alloc_edge(edge);
        let mut reapply_it = ReapplyQueueIterator::default();
        process_context.node_install_individual_link(source, edge_id, &mut reapply_it);
    }

    fn role_with_tag(tag: Cint64, complex: bool) -> Role {
        let mut role = Role::new();
        role.set_role_tag(tag).set_role_complexity(complex);
        role
    }

    #[test]
    fn classification_message_analyser_root_pseudo_model_message_requires_flag() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let adapter = SatisfiableTaskClassificationMessageAdapter::new(
            ConceptId::new(3),
            EFEXTRACTSUBSUMERSROOTNODE,
        );

        assert!(analyser
            .create_root_pseudo_model_identifier_message(&adapter, &[], &[], 0)
            .is_none());
    }

    #[test]
    fn classification_message_analyser_creates_root_pseudo_model_identifier_message() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let adapter = SatisfiableTaskClassificationMessageAdapter::new(
            ConceptId::new(3),
            EFEXTRACTIDENTIFIERPSEUDOMODEL,
        );
        let mut role_data = ClassificationClassPseudoModelRoleData::new();
        role_data.set_successor_model_id(2);
        role_data.set_lower_at_least_bound(1);
        role_data.set_upper_at_least_bound(4);
        role_data.set_lower_at_most_bound(0);
        role_data.set_upper_at_most_bound(5);
        role_data.set_deterministic(true);

        let message = analyser
            .create_root_pseudo_model_identifier_message(
                &adapter,
                &[(ConceptId::new(5), true), (ConceptId::new(7), false)],
                &[(RoleId::new(11), role_data.clone())],
                123,
            )
            .expect("pseudo-model message");

        assert_eq!(message.get_pseudo_model_concept(), ConceptId::new(3));
        assert_eq!(message.get_pseudo_model_memory_pools(), 123);
        let root_data = message
            .get_pseudo_model_hash()
            .get_pseudo_model_data(0)
            .expect("root pseudo-model data");
        assert!(root_data.has_valid_concept_map());
        assert!(root_data.has_valid_role_map());
        assert!(root_data
            .get_pseudo_model_concept_map()
            .expect("concept map")
            .get(ConceptId::new(5))
            .expect("concept 5")
            .is_deterministic());
        assert!(root_data
            .get_pseudo_model_concept_map()
            .expect("concept map")
            .get(ConceptId::new(7))
            .expect("concept 7")
            .is_non_deterministic());
        assert_eq!(
            root_data
                .get_pseudo_model_role_map()
                .expect("role map")
                .get(RoleId::new(11))
                .expect("role data")
                .get_successor_model_id(),
            2
        );
    }

    #[test]
    fn classification_message_analyser_extracts_root_pseudo_model_concepts_from_label_set() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let label_set = process_context.alloc_label_set(ReapplyConceptLabelSet::new(0));
        let mut concepts = Arena::new();
        let named_atom = concepts.push(concept_with_tag(CCATOM, 10, true));
        let unnamed_atom = concepts.push(concept_with_tag(CCATOM, 20, false));
        let sub_concept = concepts.push(concept_with_tag(CCSUB, 30, false));
        let all_concept = concepts.push(concept_with_tag(CCALL, 40, false));
        let eqcand_concept = concepts.push(concept_with_tag(CCEQCAND, 50, false));
        let impl_trig_concept = concepts.push(concept_with_tag(CCIMPLTRIG, 60, false));

        let mut deterministic_tp = DependencyTrackPoint::new(DependencyId::NONE);
        deterministic_tp.process_tag = 2;
        let deterministic_tp = process_context.alloc_track_point(deterministic_tp);
        let mut nondeterministic_tp = DependencyTrackPoint::new(DependencyId::NONE);
        nondeterministic_tp.process_tag = 9;
        let nondeterministic_tp = process_context.alloc_track_point(nondeterministic_tp);

        add_label_descriptor(
            &mut process_context,
            label_set,
            &concepts,
            named_atom,
            false,
            deterministic_tp,
        );
        add_label_descriptor(
            &mut process_context,
            label_set,
            &concepts,
            unnamed_atom,
            false,
            deterministic_tp,
        );
        add_label_descriptor(
            &mut process_context,
            label_set,
            &concepts,
            sub_concept,
            false,
            deterministic_tp,
        );
        add_label_descriptor(
            &mut process_context,
            label_set,
            &concepts,
            all_concept,
            false,
            deterministic_tp,
        );
        add_label_descriptor(
            &mut process_context,
            label_set,
            &concepts,
            eqcand_concept,
            true,
            deterministic_tp,
        );
        add_label_descriptor(
            &mut process_context,
            label_set,
            &concepts,
            impl_trig_concept,
            false,
            nondeterministic_tp,
        );

        let extracted = analyser.extract_pseudo_model_concepts_from_label_set(
            &process_context,
            label_set,
            3,
            false,
            &concepts,
        );

        assert_eq!(
            extracted,
            vec![
                (named_atom, true),
                (sub_concept, true),
                (impl_trig_concept, false)
            ]
        );
    }

    #[test]
    fn classification_message_analyser_marks_non_deterministically_connected_concepts() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let label_set = process_context.alloc_label_set(ReapplyConceptLabelSet::new(0));
        let mut concepts = Arena::new();
        let named_atom = concepts.push(concept_with_tag(CCATOM, 10, true));

        let mut deterministic_tp = DependencyTrackPoint::new(DependencyId::NONE);
        deterministic_tp.process_tag = 1;
        let deterministic_tp = process_context.alloc_track_point(deterministic_tp);
        add_label_descriptor(
            &mut process_context,
            label_set,
            &concepts,
            named_atom,
            false,
            deterministic_tp,
        );

        let extracted = analyser.extract_pseudo_model_concepts_from_label_set(
            &process_context,
            label_set,
            3,
            true,
            &concepts,
        );

        assert_eq!(extracted, vec![(named_atom, false)]);
    }

    #[test]
    fn classification_message_analyser_validates_pseudo_model_blocking_and_cache_flags() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let clean_node = add_node(&mut process_context, 0, false);
        let direct_blocked = add_node(
            &mut process_context,
            IndividualProcessNode::PRF_DIRECTBLOCKED,
            false,
        );
        let cached_valid = add_node(
            &mut process_context,
            IndividualProcessNode::PRF_COMPLETIONGRAPHCACHED,
            false,
        );
        let cached_invalidated = add_node(
            &mut process_context,
            IndividualProcessNode::PRF_COMPLETIONGRAPHCACHED
                | IndividualProcessNode::PRF_COMPLETIONGRAPHCACHINGINVALIDATED,
            false,
        );

        assert_eq!(
            analyser.evaluate_pseudo_model_map_validity(
                &process_context,
                &[(clean_node, false)],
                0,
                1,
            ),
            (true, true)
        );
        assert_eq!(
            analyser.evaluate_pseudo_model_map_validity(
                &process_context,
                &[(direct_blocked, false)],
                0,
                1,
            ),
            (false, false)
        );
        assert_eq!(
            analyser.evaluate_pseudo_model_map_validity(
                &process_context,
                &[(cached_valid, false)],
                0,
                1,
            ),
            (false, false)
        );
        assert_eq!(
            analyser.evaluate_pseudo_model_map_validity(
                &process_context,
                &[(cached_invalidated, false)],
                0,
                1,
            ),
            (true, true)
        );
    }

    #[test]
    fn classification_message_analyser_validates_pseudo_model_successor_limits() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let nominal_node = add_node(&mut process_context, 0, true);
        let clean_node = add_node(&mut process_context, 0, false);

        assert_eq!(
            analyser.evaluate_pseudo_model_map_validity(
                &process_context,
                &[(nominal_node, false)],
                0,
                1,
            ),
            (true, false)
        );
        assert_eq!(
            analyser.evaluate_pseudo_model_map_validity(
                &process_context,
                &[(clean_node, false)],
                SatisfiableTaskClassificationMessageAnalyser::MAX_PSEUDO_MODEL_DEPTH + 1,
                1,
            ),
            (true, false)
        );
        assert_eq!(
            analyser.evaluate_pseudo_model_map_validity(
                &process_context,
                &[(clean_node, false)],
                0,
                SatisfiableTaskClassificationMessageAnalyser::MAX_PSEUDO_MODEL_NODES + 1,
            ),
            (true, false)
        );
    }

    #[test]
    fn classification_message_analyser_extracts_pseudo_model_role_successor_map() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let mut roles = Arena::new();
        let role_r = roles.push(role_with_tag(10, false));
        let concepts = Arena::new();

        let root = add_identified_node(&mut process_context, 1);
        let succ = add_identified_node(&mut process_context, 2);
        let mut deterministic_tp = DependencyTrackPoint::new(DependencyId::NONE);
        deterministic_tp.process_tag = 2;
        let deterministic_tp = process_context.alloc_track_point(deterministic_tp);
        add_role_link(&mut process_context, root, succ, role_r, deterministic_tp);

        let mut process_item =
            PseudoModelAnalyseProcessItem::init_pseudo_model_analyse_process_item(0, 0);
        process_item.add_node(root, false);
        let mut next_model_id = 1;

        let (role_entries, queued_items) = analyser.extract_pseudo_model_role_successor_data(
            &process_context,
            &process_item,
            3,
            &mut next_model_id,
            &concepts,
            &roles,
        );

        assert_eq!(next_model_id, 2);
        assert_eq!(role_entries.len(), 1);
        assert_eq!(role_entries[0].0, role_r);
        let role_data = &role_entries[0].1;
        assert_eq!(role_data.get_successor_model_id(), 1);
        assert!(role_data.is_deterministic());
        assert_eq!(role_data.get_lower_at_least_bound(), 1);
        assert_eq!(role_data.get_upper_at_least_bound(), 1);
        assert_eq!(role_data.get_lower_at_most_bound(), 1);
        assert_eq!(role_data.get_upper_at_most_bound(), Cint64::MAX);
        assert_eq!(
            queued_items,
            vec![PseudoModelAnalyseProcessItem {
                pseudo_model_id: 1,
                root_distance: 1,
                nodes: vec![(succ, false)],
            }]
        );
    }

    #[test]
    fn classification_message_analyser_extracts_role_bounds_and_skips_complex_roles() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let mut roles = Arena::new();
        let simple_role = roles.push(role_with_tag(10, false));
        let complex_role = roles.push(role_with_tag(20, true));
        let mut concepts = Arena::new();

        let mut at_least = concept_with_tag(CCATLEAST, 100, false);
        at_least.set_role(simple_role).set_parameter(3);
        let at_least = concepts.push(at_least);
        let mut at_most = concept_with_tag(CCATMOST, 110, false);
        at_most.set_role(simple_role).set_parameter(2);
        let at_most = concepts.push(at_most);

        let root = add_identified_node(&mut process_context, 1);
        let simple_succ = add_identified_node(&mut process_context, 2);
        let complex_succ = add_identified_node(&mut process_context, 3);
        let mut bound_tp = DependencyTrackPoint::new(DependencyId::NONE);
        bound_tp.process_tag = 1;
        let bound_tp = process_context.alloc_track_point(bound_tp);
        let mut late_link_tp = DependencyTrackPoint::new(DependencyId::NONE);
        late_link_tp.process_tag = 9;
        let late_link_tp = process_context.alloc_track_point(late_link_tp);

        let label_set = process_context.alloc_label_set(ReapplyConceptLabelSet::new(0));
        process_context
            .node_mut(root)
            .set_reapply_concept_label_set(label_set);
        add_label_descriptor(
            &mut process_context,
            label_set,
            &concepts,
            at_least,
            false,
            bound_tp,
        );
        add_label_descriptor(
            &mut process_context,
            label_set,
            &concepts,
            at_most,
            false,
            bound_tp,
        );
        add_role_link(
            &mut process_context,
            root,
            simple_succ,
            simple_role,
            late_link_tp,
        );
        add_role_link(
            &mut process_context,
            root,
            complex_succ,
            complex_role,
            late_link_tp,
        );

        let mut process_item =
            PseudoModelAnalyseProcessItem::init_pseudo_model_analyse_process_item(0, 0);
        process_item.add_node(root, false);
        let mut next_model_id = 7;

        let (role_entries, queued_items) = analyser.extract_pseudo_model_role_successor_data(
            &process_context,
            &process_item,
            3,
            &mut next_model_id,
            &concepts,
            &roles,
        );

        assert_eq!(role_entries.len(), 1);
        assert_eq!(role_entries[0].0, simple_role);
        assert!(!role_entries.iter().any(|(role, _)| *role == complex_role));
        let role_data = &role_entries[0].1;
        assert_eq!(role_data.get_successor_model_id(), 7);
        assert!(!role_data.is_deterministic());
        assert_eq!(role_data.get_lower_at_least_bound(), 3);
        assert_eq!(role_data.get_upper_at_least_bound(), 1);
        assert_eq!(role_data.get_lower_at_most_bound(), 1);
        assert_eq!(role_data.get_upper_at_most_bound(), 2);
        assert_eq!(queued_items.len(), 1);
        assert_eq!(queued_items[0].pseudo_model_id, 7);
        assert_eq!(queued_items[0].nodes, vec![(simple_succ, true)]);
        assert_eq!(next_model_id, 8);
    }

    #[test]
    fn classification_message_analyser_builds_full_pseudo_model_identifier_message() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let mut concepts = Arena::new();
        let root_concept = concepts.push(concept_with_tag(CCATOM, 100, true));
        let succ_concept = concepts.push(concept_with_tag(CCSUB, 200, false));
        let mut roles = Arena::new();
        let role_r = roles.push(role_with_tag(10, false));

        let root = add_identified_node(&mut process_context, 1);
        let succ = add_identified_node(&mut process_context, 2);
        let mut deterministic_tp = DependencyTrackPoint::new(DependencyId::NONE);
        deterministic_tp.process_tag = 2;
        let deterministic_tp = process_context.alloc_track_point(deterministic_tp);

        let root_label_set = process_context.alloc_label_set(ReapplyConceptLabelSet::new(0));
        process_context
            .node_mut(root)
            .set_reapply_concept_label_set(root_label_set);
        add_label_descriptor(
            &mut process_context,
            root_label_set,
            &concepts,
            root_concept,
            false,
            deterministic_tp,
        );
        let succ_label_set = process_context.alloc_label_set(ReapplyConceptLabelSet::new(0));
        process_context
            .node_mut(succ)
            .set_reapply_concept_label_set(succ_label_set);
        add_label_descriptor(
            &mut process_context,
            succ_label_set,
            &concepts,
            succ_concept,
            false,
            deterministic_tp,
        );
        add_role_link(&mut process_context, root, succ, role_r, deterministic_tp);

        let adapter = SatisfiableTaskClassificationMessageAdapter::new(
            ConceptId::new(99),
            EFEXTRACTIDENTIFIERPSEUDOMODEL,
        );
        let message = analyser
            .create_pseudo_model_identifier_message_from_base_node(
                &adapter,
                &process_context,
                root,
                false,
                3,
                &concepts,
                &roles,
                555,
            )
            .expect("pseudo-model message");

        assert_eq!(message.get_pseudo_model_concept(), ConceptId::new(99));
        assert_eq!(message.get_pseudo_model_memory_pools(), 555);
        let hash = message.get_pseudo_model_hash();
        assert_eq!(hash.get_count(), 2);
        let root_model = hash.get_pseudo_model_data(0).expect("root model");
        assert!(root_model.has_valid_concept_map());
        assert!(root_model.has_valid_role_map());
        assert!(root_model
            .get_pseudo_model_concept_map()
            .expect("root concept map")
            .get(root_concept)
            .expect("root concept")
            .is_deterministic());
        let root_role = root_model
            .get_pseudo_model_role_map()
            .expect("root role map")
            .get(role_r)
            .expect("root role");
        assert_eq!(root_role.get_successor_model_id(), 1);
        assert!(root_role.is_deterministic());

        let succ_model = hash.get_pseudo_model_data(1).expect("successor model");
        assert!(succ_model.has_valid_concept_map());
        assert!(succ_model.has_valid_role_map());
        assert!(succ_model
            .get_pseudo_model_concept_map()
            .expect("successor concept map")
            .get(succ_concept)
            .expect("successor concept")
            .is_deterministic());
    }

    #[test]
    fn classification_message_analyser_pseudo_model_producer_gates_like_cpp() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let root = add_identified_node(&mut process_context, 1);
        let concepts = Arena::new();
        let roles = Arena::new();
        let no_flag_adapter =
            SatisfiableTaskClassificationMessageAdapter::new(ConceptId::new(1), 0);
        let no_concept_adapter = SatisfiableTaskClassificationMessageAdapter::new(
            ConceptId::NONE,
            EFEXTRACTIDENTIFIERPSEUDOMODEL,
        );
        let adapter = SatisfiableTaskClassificationMessageAdapter::new(
            ConceptId::new(1),
            EFEXTRACTIDENTIFIERPSEUDOMODEL,
        );

        assert!(analyser
            .create_pseudo_model_identifier_message_from_base_node(
                &no_flag_adapter,
                &process_context,
                root,
                false,
                3,
                &concepts,
                &roles,
                0,
            )
            .is_none());
        assert!(analyser
            .create_pseudo_model_identifier_message_from_base_node(
                &no_concept_adapter,
                &process_context,
                root,
                false,
                3,
                &concepts,
                &roles,
                0,
            )
            .is_none());
        assert!(analyser
            .create_pseudo_model_identifier_message_from_base_node(
                &adapter,
                &process_context,
                root,
                true,
                3,
                &concepts,
                &roles,
                0,
            )
            .is_none());
    }

    #[test]
    fn classification_message_analyser_wraps_pseudo_model_message_in_linker() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let mut concepts = Arena::new();
        let root_concept = concepts.push(concept_with_tag(CCATOM, 100, true));
        let roles = Arena::new();
        let root = add_identified_node(&mut process_context, 1);
        let mut deterministic_tp = DependencyTrackPoint::new(DependencyId::NONE);
        deterministic_tp.process_tag = 1;
        let deterministic_tp = process_context.alloc_track_point(deterministic_tp);
        let root_label_set = process_context.alloc_label_set(ReapplyConceptLabelSet::new(0));
        process_context
            .node_mut(root)
            .set_reapply_concept_label_set(root_label_set);
        add_label_descriptor(
            &mut process_context,
            root_label_set,
            &concepts,
            root_concept,
            false,
            deterministic_tp,
        );
        let adapter = SatisfiableTaskClassificationMessageAdapter::new(
            ConceptId::new(7),
            EFEXTRACTIDENTIFIERPSEUDOMODEL,
        );

        let linker = analyser
            .create_pseudo_model_identifier_message_linker_from_base_node(
                &adapter,
                &process_context,
                root,
                false,
                3,
                &concepts,
                &roles,
                606,
            )
            .expect("message linker");

        assert_eq!(linker.len(), 1);
        let Some(ClassificationMessageDataPayload::PseudoModelIdentifier(message)) =
            linker.iter().next()
        else {
            panic!("expected pseudomodel message");
        };
        assert_eq!(message.get_pseudo_model_concept(), ConceptId::new(7));
        assert_eq!(message.get_pseudo_model_memory_pools(), 606);
        assert!(message
            .get_pseudo_model_hash()
            .get_pseudo_model_data(0)
            .expect("root model")
            .get_pseudo_model_concept_map()
            .expect("root concept map")
            .get(root_concept)
            .is_some());
    }

    #[test]
    fn classification_message_analyser_merges_message_linkers_in_cpp_order() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let subsum = ClassificationMessageDataLinker::from_message(
            ClassificationMessageDataPayload::Header(ClassificationMessageData::new(
                ClassificationMessageDataType::TellClassSubsumption,
            )),
        );
        let pm = ClassificationMessageDataLinker::from_message(
            ClassificationMessageDataPayload::Header(ClassificationMessageData::new(
                ClassificationMessageDataType::TellClassPseudoModelIdentifiers,
            )),
        );
        let poss = ClassificationMessageDataLinker::from_message(
            ClassificationMessageDataPayload::Header(ClassificationMessageData::new(
                ClassificationMessageDataType::TellClassUpdatePossibleSubsumption,
            )),
        );

        let merged = analyser
            .merge_classification_message_data_linkers(Some(subsum), Some(pm), Some(poss))
            .expect("merged linker");

        assert_eq!(
            merged.message_types(),
            vec![
                ClassificationMessageDataType::TellClassUpdatePossibleSubsumption,
                ClassificationMessageDataType::TellClassPseudoModelIdentifiers,
                ClassificationMessageDataType::TellClassSubsumption,
            ]
        );
    }

    #[test]
    fn classification_message_analyser_corrects_individual_id_over_deterministic_merge_chain() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let mut node_vector = IndividualProcessNodeVector::new();
        let base = add_identified_node(&mut process_context, 10);
        let middle = add_identified_node(&mut process_context, 20);
        let representative = add_identified_node(&mut process_context, 30);
        let deterministic_track = add_dependency_track_point(
            &mut process_context,
            DepKind::And,
            base,
            TrackPointId::NONE,
        );
        process_context
            .node_mut(base)
            .set_merged_into_individual_node_id(20)
            .set_merged_dependency_track_point(deterministic_track);
        process_context
            .node_mut(middle)
            .set_merged_into_individual_node_id(30)
            .set_merged_dependency_track_point(deterministic_track);
        node_vector
            .set_data(10, base)
            .set_data(20, middle)
            .set_data(30, representative);

        let corrected = analyser
            .get_corrected_individual_id(&process_context, base, &node_vector)
            .expect("corrected individual");

        assert_eq!(
            corrected,
            ClassificationAnalyserCorrectedIndividual {
                node: representative,
                individual_id: 30,
                nondeterministically_merged: false,
            }
        );
    }

    #[test]
    fn classification_message_analyser_corrected_individual_marks_nondeterministic_merges() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let mut node_vector = IndividualProcessNodeVector::new();
        let null_dep_base = add_identified_node(&mut process_context, 40);
        let branch_dep_base = add_identified_node(&mut process_context, 50);
        let representative = add_identified_node(&mut process_context, 60);
        let mut positive_branch_track = DependencyTrackPoint::new(DependencyId::NONE);
        positive_branch_track.process_tag = 1;
        let positive_branch_track = process_context.alloc_track_point(positive_branch_track);
        process_context
            .node_mut(null_dep_base)
            .set_merged_into_individual_node_id(60)
            .set_merged_dependency_track_point(TrackPointId::NONE);
        process_context
            .node_mut(branch_dep_base)
            .set_merged_into_individual_node_id(60)
            .set_merged_dependency_track_point(positive_branch_track);
        node_vector
            .set_data(40, null_dep_base)
            .set_data(50, branch_dep_base)
            .set_data(60, representative);

        assert!(
            analyser
                .get_corrected_individual_id(&process_context, null_dep_base, &node_vector)
                .expect("null dependency merge")
                .nondeterministically_merged
        );
        assert!(
            analyser
                .get_corrected_individual_id(&process_context, branch_dep_base, &node_vector)
                .expect("branch dependency merge")
                .nondeterministically_merged
        );
    }

    #[test]
    fn classification_message_analyser_corrected_individual_rejects_missing_vector_entry() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let node_vector = IndividualProcessNodeVector::new();
        let base = add_identified_node(&mut process_context, 70);

        assert_eq!(
            analyser.get_corrected_individual_id(&process_context, base, &node_vector),
            None
        );
    }

    #[test]
    fn classification_message_analyser_root_branch_uses_corrected_base_and_clamps_nondet_merge() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let mut node_vector = IndividualProcessNodeVector::new();
        let mut concepts = Arena::new();
        let testing = concepts.push(concept_with_tag(CCATOM, 10, true));
        let late_subsumer = concepts.push(concept_with_tag(CCATOM, 20, true));
        let constructed = add_identified_node(&mut process_context, 1);
        let representative = add_identified_node(&mut process_context, 2);
        let mut merge_track = DependencyTrackPoint::new(DependencyId::NONE);
        merge_track.process_tag = 1;
        let merge_track = process_context.alloc_track_point(merge_track);
        process_context
            .node_mut(constructed)
            .set_merged_into_individual_node_id(2)
            .set_merged_dependency_track_point(merge_track);
        node_vector
            .set_data(1, constructed)
            .set_data(2, representative);

        let label_set = process_context.alloc_label_set(ReapplyConceptLabelSet::new(0));
        process_context
            .node_mut(representative)
            .set_reapply_concept_label_set(label_set);
        let mut root_track = DependencyTrackPoint::new(DependencyId::NONE);
        root_track.process_tag = 0;
        let root_track = process_context.alloc_track_point(root_track);
        let mut late_track = DependencyTrackPoint::new(DependencyId::NONE);
        late_track.process_tag = 3;
        let late_track = process_context.alloc_track_point(late_track);
        add_label_descriptor(
            &mut process_context,
            label_set,
            &concepts,
            testing,
            false,
            root_track,
        );
        add_label_descriptor(
            &mut process_context,
            label_set,
            &concepts,
            late_subsumer,
            false,
            late_track,
        );
        let adapter =
            SatisfiableTaskClassificationMessageAdapter::new(testing, EFEXTRACTSUBSUMERSROOTNODE);

        let result = analyser
            .create_root_classification_message_linkers_from_constructed_node(
                &adapter,
                &process_context,
                constructed,
                &node_vector,
                5,
                &std::collections::HashMap::new(),
                &std::collections::HashMap::new(),
                &concepts,
            )
            .expect("root branch result");

        assert_eq!(result.corrected_individual.node, representative);
        assert_eq!(result.max_deterministic_branch_tag, 0);
        let subsum_linker = result
            .subsum_message_data_linker
            .expect("root class-subsumption linker");
        let mut messages = subsum_linker.iter();
        let Some(ClassificationMessageDataPayload::ClassSubsumption(message)) = messages.next()
        else {
            panic!("expected root class-subsumption message");
        };
        assert_eq!(message.get_subsumed_concept(), testing);
        assert_eq!(message.get_class_subsumer_list(), None);
        assert!(messages.next().is_none());
        assert!(result.poss_subsum_message_data_linker.is_none());
    }

    #[test]
    fn classification_message_analyser_root_branch_possible_only_still_emits_root_class_message() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let mut node_vector = IndividualProcessNodeVector::new();
        let mut concepts = Arena::new();
        let testing = concepts.push(concept_with_tag(CCATOM, 10, true));
        let possible = concepts.push(concept_with_tag(CCATOM, 20, true));
        let negated = concepts.push(concept_with_tag(CCATOM, 30, true));
        let root = add_identified_node(&mut process_context, 1);
        node_vector.set_data(1, root);
        let label_set = process_context.alloc_label_set(ReapplyConceptLabelSet::new(0));
        process_context
            .node_mut(root)
            .set_reapply_concept_label_set(label_set);
        let mut track = DependencyTrackPoint::new(DependencyId::NONE);
        track.process_tag = 0;
        let track = process_context.alloc_track_point(track);
        add_label_descriptor(
            &mut process_context,
            label_set,
            &concepts,
            testing,
            false,
            track,
        );
        add_label_descriptor(
            &mut process_context,
            label_set,
            &concepts,
            possible,
            false,
            track,
        );
        add_label_descriptor(
            &mut process_context,
            label_set,
            &concepts,
            negated,
            true,
            track,
        );
        let adapter = SatisfiableTaskClassificationMessageAdapter::new(
            testing,
            EFEXTRACTPOSSIBLESUBSUMERSROOTNODE,
        );

        let result = analyser
            .create_root_classification_message_linkers_from_constructed_node(
                &adapter,
                &process_context,
                root,
                &node_vector,
                0,
                &std::collections::HashMap::new(),
                &std::collections::HashMap::new(),
                &concepts,
            )
            .expect("root branch result");

        let subsum_linker = result
            .subsum_message_data_linker
            .expect("root class-subsumption linker");
        let Some(ClassificationMessageDataPayload::ClassSubsumption(message)) =
            subsum_linker.iter().next()
        else {
            panic!("expected root class-subsumption message");
        };
        assert_eq!(message.get_subsumed_concept(), testing);
        assert_eq!(message.get_class_subsumer_list(), None);

        let poss_linker = result
            .poss_subsum_message_data_linker
            .expect("root possible-subsumption linker");
        let subsumed = poss_linker
            .iter()
            .map(|payload| match payload {
                ClassificationMessageDataPayload::InitializePossibleClassSubsumption(message) => {
                    message.get_subsumed_concept()
                }
                _ => panic!("expected possible-subsumption init message"),
            })
            .collect::<Vec<_>>();
        assert_eq!(subsumed, vec![possible, testing]);
    }

    #[test]
    fn classification_message_analyser_bounded_integration_delivers_root_other_and_pseudomodel() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let mut node_vector = IndividualProcessNodeVector::new();
        let mut concepts = Arena::new();
        let mut ontology = OntologyArenas::new();
        let testing = concepts.push(concept_with_tag(CCATOM, 10, true));
        assert_eq!(
            ontology.alloc_concept(concept_with_tag(CCATOM, 10, true)),
            testing
        );
        let root_subsumer = concepts.push(concept_with_tag(CCATOM, 20, true));
        assert_eq!(
            ontology.alloc_concept(concept_with_tag(CCATOM, 20, true)),
            root_subsumer
        );
        let other_analyse = concepts.push(concept_with_tag(CCATOM, 30, true));
        assert_eq!(
            ontology.alloc_concept(concept_with_tag(CCATOM, 30, true)),
            other_analyse
        );
        let other_subsumer = concepts.push(concept_with_tag(CCATOM, 40, true));
        assert_eq!(
            ontology.alloc_concept(concept_with_tag(CCATOM, 40, true)),
            other_subsumer
        );
        let mut roles = Arena::new();
        let role = roles.push(role_with_tag(5, false));

        let root = add_identified_node(&mut process_context, 1);
        let other = add_identified_node(&mut process_context, 2);
        process_context
            .node_mut(root)
            .set_individual_ancestor_depth(0);
        process_context
            .node_mut(other)
            .set_individual_ancestor_depth(1);
        node_vector.set_data(1, root).set_data(2, other);

        let root_label_set = process_context.alloc_label_set(ReapplyConceptLabelSet::new(0));
        process_context
            .node_mut(root)
            .set_reapply_concept_label_set(root_label_set);
        let root_track = add_dependency_track_point(
            &mut process_context,
            DepKind::And,
            root,
            TrackPointId::NONE,
        );
        add_label_descriptor(
            &mut process_context,
            root_label_set,
            &concepts,
            testing,
            false,
            root_track,
        );
        add_label_descriptor(
            &mut process_context,
            root_label_set,
            &concepts,
            root_subsumer,
            false,
            root_track,
        );

        let other_label_set = process_context.alloc_label_set(ReapplyConceptLabelSet::new(0));
        process_context
            .node_mut(other)
            .set_reapply_concept_label_set(other_label_set);
        let ancestor_track = add_dependency_track_point(
            &mut process_context,
            DepKind::Some,
            root,
            TrackPointId::NONE,
        );
        add_label_descriptor(
            &mut process_context,
            other_label_set,
            &concepts,
            other_analyse,
            false,
            ancestor_track,
        );
        let same_branch_nonancestor_track = add_dependency_track_point(
            &mut process_context,
            DepKind::And,
            other,
            TrackPointId::NONE,
        );
        add_label_descriptor(
            &mut process_context,
            other_label_set,
            &concepts,
            other_subsumer,
            false,
            same_branch_nonancestor_track,
        );
        add_role_link(&mut process_context, root, other, role, root_track);

        let adapter = SatisfiableTaskClassificationMessageAdapter::new_with_handles(
            testing,
            71,
            73,
            std::collections::HashMap::new(),
            EFEXTRACTSUBSUMERSROOTNODE
                | EFEXTRACTPOSSIBLESUBSUMERSROOTNODE
                | EFEXTRACTSUBSUMERSOTHERNODES
                | EFEXTRACTPOSSIBLESUBSUMERSOTHERNODES
                | EFEXTRACTOTHERNODESSINGLEDEPENDENCY
                | EFEXTRACTIDENTIFIERPSEUDOMODEL,
        );
        let mut required = std::collections::HashSet::new();
        required.insert(other_analyse);
        let mut observer = RecordingClassificationMessageDataObserver::new();

        let result = analyser
            .analyse_satisfiable_task_classification_messages_bounded(
                &adapter,
                &process_context,
                &ontology,
                root,
                &node_vector,
                0,
                &std::collections::HashMap::new(),
                &std::collections::HashMap::new(),
                &required,
                &[other],
                &concepts,
                &roles,
                91,
                Some(&mut observer),
            )
            .expect("bounded analyser result");

        assert_eq!(result.corrected_individual.node, root);
        assert_eq!(result.other_node_visit_count, 1);
        assert!(result.output.delivered_to_observer);
        assert_eq!(observer.get_told_messages().len(), 1);
        assert_eq!(observer.get_told_messages()[0].0, 71);
        assert_eq!(observer.get_told_messages()[0].2, 91);
        let init_subsumed = observer.get_told_messages()[0]
            .1
            .iter()
            .filter_map(|payload| match payload {
                ClassificationMessageDataPayload::InitializePossibleClassSubsumption(message) => {
                    Some(message.get_subsumed_concept())
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(init_subsumed, vec![other_analyse, root_subsumer, testing]);
        let message_types = observer.get_told_messages()[0].1.message_types();
        assert_eq!(
            message_types,
            vec![
                ClassificationMessageDataType::TellClassInitializePossibleSubsumption,
                ClassificationMessageDataType::TellClassInitializePossibleSubsumption,
                ClassificationMessageDataType::TellClassInitializePossibleSubsumption,
                ClassificationMessageDataType::TellClassPseudoModelIdentifiers,
                ClassificationMessageDataType::TellClassSubsumption,
                ClassificationMessageDataType::TellClassSubsumption,
            ]
        );
    }

    #[test]
    fn classification_message_analyser_bounded_integration_releases_without_requested_messages() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let mut node_vector = IndividualProcessNodeVector::new();
        let mut concepts = Arena::new();
        let mut ontology = OntologyArenas::new();
        let testing = concepts.push(concept_with_tag(CCATOM, 10, true));
        assert_eq!(
            ontology.alloc_concept(concept_with_tag(CCATOM, 10, true)),
            testing
        );
        let roles = Arena::new();
        let root = add_identified_node(&mut process_context, 1);
        node_vector.set_data(1, root);
        let adapter = SatisfiableTaskClassificationMessageAdapter::new_with_handles(
            testing,
            71,
            73,
            std::collections::HashMap::new(),
            0,
        );
        let mut observer = RecordingClassificationMessageDataObserver::new();

        let result = analyser
            .analyse_satisfiable_task_classification_messages_bounded(
                &adapter,
                &process_context,
                &ontology,
                root,
                &node_vector,
                0,
                &std::collections::HashMap::new(),
                &std::collections::HashMap::new(),
                &std::collections::HashSet::new(),
                &[],
                &concepts,
                &roles,
                93,
                Some(&mut observer),
            )
            .expect("bounded analyser result");

        assert_eq!(
            result.output,
            ClassificationAnalyserMessageOutputResult {
                had_message_data: false,
                delivered_to_observer: false,
                released_memory_pool: Some(93),
            }
        );
        assert!(observer.get_told_messages().is_empty());
    }

    #[test]
    fn classification_message_analyser_classifier_references_drive_other_node_possible_messages() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let mut node_vector = IndividualProcessNodeVector::new();
        let mut concepts = Arena::new();
        let mut ontology = OntologyArenas::new();
        let testing = concepts.push(concept_with_tag(CCATOM, 10, true));
        assert_eq!(
            ontology.alloc_concept(concept_with_tag(CCATOM, 10, true)),
            testing
        );
        let other_analyse = concepts.push(concept_with_tag(CCATOM, 30, true));
        assert_eq!(
            ontology.alloc_concept(concept_with_tag(CCATOM, 30, true)),
            other_analyse
        );
        let mut roles = Arena::new();
        let role = roles.push(role_with_tag(5, false));

        let root = add_identified_node(&mut process_context, 1);
        let other = add_identified_node(&mut process_context, 2);
        process_context
            .node_mut(root)
            .set_individual_ancestor_depth(0);
        process_context
            .node_mut(other)
            .set_individual_ancestor_depth(1);
        node_vector.set_data(1, root).set_data(2, other);

        let other_label_set = process_context.alloc_label_set(ReapplyConceptLabelSet::new(0));
        process_context
            .node_mut(other)
            .set_reapply_concept_label_set(other_label_set);
        let ancestor_track = add_dependency_track_point(
            &mut process_context,
            DepKind::Some,
            root,
            TrackPointId::NONE,
        );
        add_label_descriptor(
            &mut process_context,
            other_label_set,
            &concepts,
            other_analyse,
            false,
            ancestor_track,
        );
        add_role_link(&mut process_context, root, other, role, ancestor_track);

        let mut con_ref_hash = std::collections::HashMap::new();
        con_ref_hash.insert(other_analyse, 0);
        let adapter = SatisfiableTaskClassificationMessageAdapter::new_with_handles(
            testing,
            71,
            73,
            con_ref_hash,
            EFEXTRACTPOSSIBLESUBSUMERSOTHERNODES | EFEXTRACTOTHERNODESSINGLEDEPENDENCY,
        );
        let concept_process_datas = Arena::<ConceptProcessData>::new();
        let concept_reference_linking_datas = Arena::<ConceptSaturationReferenceLinkingData>::new();
        let testing_items = vec![OptimizedKPSetClassTestingItem::new()];
        let mut observer = RecordingClassificationMessageDataObserver::new();

        let result = analyser
            .analyse_satisfiable_task_classification_messages_with_classifier_references(
                &adapter,
                &process_context,
                &ontology,
                root,
                &node_vector,
                0,
                &std::collections::HashMap::new(),
                &std::collections::HashMap::new(),
                &[other],
                &concepts,
                &concept_process_datas,
                &concept_reference_linking_datas,
                &testing_items,
                &roles,
                95,
                Some(&mut observer),
            )
            .expect("classifier-reference analyser result");

        assert_eq!(result.corrected_individual.node, root);
        assert_eq!(result.other_node_visit_count, 1);
        assert!(result.output.delivered_to_observer);
        assert_eq!(observer.get_told_messages().len(), 1);
        assert_eq!(observer.get_told_messages()[0].0, 71);
        assert_eq!(observer.get_told_messages()[0].2, 95);
        assert_eq!(
            observer.get_told_messages()[0].1.message_types(),
            vec![ClassificationMessageDataType::TellClassInitializePossibleSubsumption]
        );
    }

    #[test]
    fn classification_message_analyser_live_other_node_wrapper_discovers_graph_successors() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let mut node_vector = IndividualProcessNodeVector::new();
        let mut concepts = Arena::new();
        let mut ontology = OntologyArenas::new();
        let testing = concepts.push(concept_with_tag(CCATOM, 10, true));
        assert_eq!(
            ontology.alloc_concept(concept_with_tag(CCATOM, 10, true)),
            testing
        );
        let other_analyse = concepts.push(concept_with_tag(CCATOM, 30, true));
        assert_eq!(
            ontology.alloc_concept(concept_with_tag(CCATOM, 30, true)),
            other_analyse
        );
        let mut roles = Arena::new();
        let role = roles.push(role_with_tag(5, false));

        let root = add_identified_node(&mut process_context, 1);
        let other = add_identified_node(&mut process_context, 2);
        process_context
            .node_mut(root)
            .set_individual_ancestor_depth(0);
        process_context
            .node_mut(other)
            .set_individual_ancestor_depth(1);
        node_vector.set_data(1, root).set_data(2, other);

        let other_label_set = process_context.alloc_label_set(ReapplyConceptLabelSet::new(0));
        process_context
            .node_mut(other)
            .set_reapply_concept_label_set(other_label_set);
        let ancestor_track = add_dependency_track_point(
            &mut process_context,
            DepKind::Some,
            root,
            TrackPointId::NONE,
        );
        add_label_descriptor(
            &mut process_context,
            other_label_set,
            &concepts,
            other_analyse,
            false,
            ancestor_track,
        );
        add_role_link(&mut process_context, root, other, role, ancestor_track);

        let mut con_ref_hash = std::collections::HashMap::new();
        con_ref_hash.insert(other_analyse, 0);
        let adapter = SatisfiableTaskClassificationMessageAdapter::new_with_handles(
            testing,
            71,
            73,
            con_ref_hash,
            EFEXTRACTPOSSIBLESUBSUMERSOTHERNODES | EFEXTRACTOTHERNODESSINGLEDEPENDENCY,
        );
        let concept_process_datas = Arena::<ConceptProcessData>::new();
        let concept_reference_linking_datas = Arena::<ConceptSaturationReferenceLinkingData>::new();
        let testing_items = vec![OptimizedKPSetClassTestingItem::new()];
        let mut observer = RecordingClassificationMessageDataObserver::new();

        let result = analyser
            .analyse_satisfiable_task_classification_messages_with_live_other_nodes(
                &adapter,
                &process_context,
                &ontology,
                root,
                &node_vector,
                0,
                &std::collections::HashMap::new(),
                &concepts,
                &concept_process_datas,
                &concept_reference_linking_datas,
                &testing_items,
                &roles,
                101,
                Some(&mut observer),
            )
            .expect("live other-node analyser result");

        assert_eq!(result.corrected_individual.node, root);
        assert_eq!(result.other_node_visit_count, 1);
        assert!(result.output.delivered_to_observer);
        assert_eq!(observer.get_told_messages().len(), 1);
        assert_eq!(observer.get_told_messages()[0].0, 71);
        assert_eq!(observer.get_told_messages()[0].2, 101);
        assert_eq!(
            observer.get_told_messages()[0].1.message_types(),
            vec![ClassificationMessageDataType::TellClassInitializePossibleSubsumption]
        );
    }

    #[test]
    fn classification_message_analyser_live_wrapper_uses_ontology_equivalent_non_candidates() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let mut node_vector = IndividualProcessNodeVector::new();
        let mut concepts = Arena::new();
        let mut ontology = OntologyArenas::new();
        let testing = concepts.push(concept_with_tag(CCATOM, 10, true));
        let operand = concepts.push(concept_with_tag(CCATOM, 20, true));
        let mut filtered_equivalence = concept_with_tag(CCEQ, 30, true);
        filtered_equivalence.add_operand_linker(operand, false);
        let filtered_equivalence = concepts.push(filtered_equivalence);
        ontology.insert_equivalent_concept_non_candidate(filtered_equivalence);
        let roles = Arena::new();
        let concept_process_datas = Arena::<ConceptProcessData>::new();
        let concept_reference_linking_datas = Arena::<ConceptSaturationReferenceLinkingData>::new();
        let saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let testing_items = vec![OptimizedKPSetClassTestingItem::new()];

        let root = add_identified_node(&mut process_context, 1);
        node_vector.set_data(1, root);
        let root_label_set = process_context.alloc_label_set(ReapplyConceptLabelSet::new(0));
        process_context
            .node_mut(root)
            .set_reapply_concept_label_set(root_label_set);
        add_label_descriptor(
            &mut process_context,
            root_label_set,
            &concepts,
            testing,
            false,
            TrackPointId::NONE,
        );
        add_label_descriptor(
            &mut process_context,
            root_label_set,
            &concepts,
            operand,
            true,
            TrackPointId::NONE,
        );
        let adapter = SatisfiableTaskClassificationMessageAdapter::new_with_handles(
            testing,
            71,
            73,
            std::collections::HashMap::new(),
            EFEXTRACTPOSSIBLESUBSUMERSROOTNODE,
        );
        let mut observer = RecordingClassificationMessageDataObserver::new();

        let result = analyser
            .analyse_satisfiable_task_classification_messages_with_live_other_nodes_and_live_equivalent_non_candidates(
                &adapter,
                &mut process_context,
                &ontology,
                root,
                &node_vector,
                0,
                &concepts,
                &concept_process_datas,
                &concept_reference_linking_datas,
                &saturation_reference_linkings,
                &testing_items,
                &roles,
                false,
                103,
                Some(&mut observer),
            )
            .expect("live equivalent non-candidate analyser result");

        assert_eq!(result.corrected_individual.node, root);
        assert!(result.output.delivered_to_observer);
        let messages = observer.get_told_messages();
        assert_eq!(messages.len(), 1);
        let init_message = messages[0]
            .1
            .iter()
            .find_map(|payload| match payload {
                ClassificationMessageDataPayload::InitializePossibleClassSubsumption(message) => {
                    Some(message)
                }
                _ => None,
            })
            .expect("initialize possible-subsumption message");
        assert!(init_message.has_eq_concepts_non_candidate_poss_subsumers());
        assert!(init_message
            .get_class_eq_concept_non_candidate_possible_subsumer_list()
            .is_none());
    }

    #[test]
    fn classification_message_analyser_live_wrapper_suppresses_pseudomodel_for_value_space_triggers(
    ) {
        fn run(has_value_space_triggers: bool) -> Vec<ClassificationMessageDataType> {
            let analyser = SatisfiableTaskClassificationMessageAnalyser;
            let mut process_context = ProcessContext::new();
            let mut node_vector = IndividualProcessNodeVector::new();
            let mut concepts = Arena::new();
            let ontology = OntologyArenas::new();
            let testing = concepts.push(concept_with_tag(CCATOM, 10, true));
            let subsumer = concepts.push(concept_with_tag(CCATOM, 20, true));
            let roles = Arena::new();
            let concept_process_datas = Arena::<ConceptProcessData>::new();
            let concept_reference_linking_datas =
                Arena::<ConceptSaturationReferenceLinkingData>::new();
            let saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
            let testing_items = vec![OptimizedKPSetClassTestingItem::new()];

            let root = add_identified_node(&mut process_context, 1);
            node_vector.set_data(1, root);
            let root_label_set = process_context.alloc_label_set(ReapplyConceptLabelSet::new(0));
            process_context
                .node_mut(root)
                .set_reapply_concept_label_set(root_label_set);
            let deterministic_track = add_branch_track_point(&mut process_context, 0);
            add_label_descriptor(
                &mut process_context,
                root_label_set,
                &concepts,
                testing,
                false,
                deterministic_track,
            );
            add_label_descriptor(
                &mut process_context,
                root_label_set,
                &concepts,
                subsumer,
                false,
                deterministic_track,
            );
            let adapter = SatisfiableTaskClassificationMessageAdapter::new_with_handles(
                testing,
                71,
                73,
                std::collections::HashMap::new(),
                EFEXTRACTSUBSUMERSROOTNODE | EFEXTRACTIDENTIFIERPSEUDOMODEL,
            );
            let mut observer = RecordingClassificationMessageDataObserver::new();

            let result = analyser
                .analyse_satisfiable_task_classification_messages_with_live_other_nodes_and_live_equivalent_non_candidates(
                    &adapter,
                    &mut process_context,
                    &ontology,
                    root,
                    &node_vector,
                    0,
                    &concepts,
                    &concept_process_datas,
                    &concept_reference_linking_datas,
                    &saturation_reference_linkings,
                    &testing_items,
                    &roles,
                    has_value_space_triggers,
                    107,
                    Some(&mut observer),
                )
                .expect("live analyser result");
            assert!(result.output.delivered_to_observer);
            observer.get_told_messages()[0].1.message_types()
        }

        assert_eq!(
            run(false),
            vec![
                ClassificationMessageDataType::TellClassPseudoModelIdentifiers,
                ClassificationMessageDataType::TellClassSubsumption,
            ]
        );
        assert_eq!(
            run(true),
            vec![ClassificationMessageDataType::TellClassSubsumption]
        );
    }

    #[test]
    fn classification_message_analyser_task_context_entry_reads_adapter_and_databox() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut calc_context = CalculationAlgorithmContext::new();
        let testing = calc_context
            .ontology_arenas
            .alloc_concept(concept_with_tag(CCATOM, 10, true));
        let subsumer = calc_context
            .ontology_arenas
            .alloc_concept(concept_with_tag(CCATOM, 20, true));

        let root = add_identified_node(&mut calc_context.used_process_context, 1);
        let root_label_set = calc_context
            .used_process_context
            .alloc_label_set(ReapplyConceptLabelSet::new(0));
        calc_context
            .used_process_context
            .node_mut(root)
            .set_reapply_concept_label_set(root_label_set);
        let deterministic_track = add_branch_track_point(&mut calc_context.used_process_context, 0);
        add_label_descriptor(
            &mut calc_context.used_process_context,
            root_label_set,
            calc_context.ontology_arenas.concepts(),
            testing,
            false,
            deterministic_track,
        );
        add_label_descriptor(
            &mut calc_context.used_process_context,
            root_label_set,
            calc_context.ontology_arenas.concepts(),
            subsumer,
            false,
            deterministic_track,
        );

        let adapter = calc_context.alloc_classification_message_adapter(
            SatisfiableTaskClassificationMessageAdapter::new_with_handles(
                testing,
                71,
                73,
                std::collections::HashMap::new(),
                EFEXTRACTSUBSUMERSROOTNODE | EFEXTRACTIDENTIFIERPSEUDOMODEL,
            ),
        );
        let mut data_box = ProcessingDataBox::new();
        data_box
            .set_constructed_individual_node(root)
            .set_maximum_deterministic_branch_tag(0);
        data_box
            .individual_process_node_vector_mut()
            .set_data(1, root);
        let mut task = SatisfiableCalculationTask::new();
        task.set_classification_message_adapter(adapter)
            .set_processing_data_box_state(data_box);
        let task_id = calc_context.alloc_sat_calc_task(task);
        let mut observer = RecordingClassificationMessageDataObserver::new();

        let result = analyser
            .analyse_satisfiable_task_from_context(
                task_id,
                &mut calc_context,
                &[OptimizedKPSetClassTestingItem::new()],
                109,
                Some(&mut observer),
            )
            .expect("task-context analyser result");

        assert_eq!(result.corrected_individual.node, root);
        assert!(result.output.delivered_to_observer);
        assert_eq!(observer.get_told_messages().len(), 1);
        assert_eq!(observer.get_told_messages()[0].0, 71);
        assert_eq!(observer.get_told_messages()[0].2, 109);
        assert_eq!(
            observer.get_told_messages()[0].1.message_types(),
            vec![
                ClassificationMessageDataType::TellClassPseudoModelIdentifiers,
                ClassificationMessageDataType::TellClassSubsumption,
            ]
        );
    }

    #[test]
    fn classification_message_analyser_task_context_entry_reads_mbox_value_space_triggers() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut calc_context = CalculationAlgorithmContext::new();
        let testing = calc_context
            .ontology_arenas
            .alloc_concept(concept_with_tag(CCATOM, 181, true));
        let subsumer = calc_context
            .ontology_arenas
            .alloc_concept(concept_with_tag(CCATOM, 191, true));
        calc_context
            .ontology_arenas
            .get_value_spaces_triggers_mut(true);

        let root = add_identified_node(&mut calc_context.used_process_context, 1);
        let root_label_set = calc_context
            .used_process_context
            .alloc_label_set(ReapplyConceptLabelSet::new(0));
        calc_context
            .used_process_context
            .node_mut(root)
            .set_reapply_concept_label_set(root_label_set);
        let deterministic_track = add_branch_track_point(&mut calc_context.used_process_context, 0);
        add_label_descriptor(
            &mut calc_context.used_process_context,
            root_label_set,
            calc_context.ontology_arenas.concepts(),
            testing,
            false,
            deterministic_track,
        );
        add_label_descriptor(
            &mut calc_context.used_process_context,
            root_label_set,
            calc_context.ontology_arenas.concepts(),
            subsumer,
            false,
            deterministic_track,
        );

        let adapter = calc_context.alloc_classification_message_adapter(
            SatisfiableTaskClassificationMessageAdapter::new_with_handles(
                testing,
                181,
                191,
                std::collections::HashMap::new(),
                EFEXTRACTSUBSUMERSROOTNODE | EFEXTRACTIDENTIFIERPSEUDOMODEL,
            ),
        );
        let mut data_box = ProcessingDataBox::new();
        data_box
            .set_constructed_individual_node(root)
            .set_maximum_deterministic_branch_tag(0);
        data_box
            .individual_process_node_vector_mut()
            .set_data(1, root);
        let mut task = SatisfiableCalculationTask::new();
        task.set_classification_message_adapter(adapter)
            .set_processing_data_box_state(data_box);
        let task_id = calc_context.alloc_sat_calc_task(task);
        let mut observer = RecordingClassificationMessageDataObserver::new();

        let result = analyser
            .analyse_satisfiable_task_from_context(
                task_id,
                &mut calc_context,
                &[OptimizedKPSetClassTestingItem::new()],
                211,
                Some(&mut observer),
            )
            .expect("task-context analyser result");

        assert_eq!(result.corrected_individual.node, root);
        assert!(result.output.delivered_to_observer);
        assert_eq!(observer.get_told_messages().len(), 1);
        assert_eq!(
            observer.get_told_messages()[0].1.message_types(),
            vec![ClassificationMessageDataType::TellClassSubsumption]
        );
    }

    #[test]
    fn classification_message_analyser_task_context_entry_resolves_registered_observer() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut calc_context = CalculationAlgorithmContext::new();
        let mut observer_registry = ClassificationMessageDataObserverRegistry::new();
        let observer_handle =
            observer_registry.alloc_observer(RecordingClassificationMessageDataObserver::new());
        let testing = calc_context
            .ontology_arenas
            .alloc_concept(concept_with_tag(CCATOM, 223, true));
        let subsumer = calc_context
            .ontology_arenas
            .alloc_concept(concept_with_tag(CCATOM, 227, true));

        let root = add_identified_node(&mut calc_context.used_process_context, 1);
        let root_label_set = calc_context
            .used_process_context
            .alloc_label_set(ReapplyConceptLabelSet::new(0));
        calc_context
            .used_process_context
            .node_mut(root)
            .set_reapply_concept_label_set(root_label_set);
        let deterministic_track = add_branch_track_point(&mut calc_context.used_process_context, 0);
        add_label_descriptor(
            &mut calc_context.used_process_context,
            root_label_set,
            calc_context.ontology_arenas.concepts(),
            testing,
            false,
            deterministic_track,
        );
        add_label_descriptor(
            &mut calc_context.used_process_context,
            root_label_set,
            calc_context.ontology_arenas.concepts(),
            subsumer,
            false,
            deterministic_track,
        );

        let adapter = calc_context.alloc_classification_message_adapter(
            SatisfiableTaskClassificationMessageAdapter::new_with_handles(
                testing,
                223,
                observer_handle,
                std::collections::HashMap::new(),
                EFEXTRACTSUBSUMERSROOTNODE,
            ),
        );
        let mut data_box = ProcessingDataBox::new();
        data_box
            .set_constructed_individual_node(root)
            .set_maximum_deterministic_branch_tag(0);
        data_box
            .individual_process_node_vector_mut()
            .set_data(1, root);
        let mut task = SatisfiableCalculationTask::new();
        task.set_classification_message_adapter(adapter)
            .set_processing_data_box_state(data_box);
        let task_id = calc_context.alloc_sat_calc_task(task);

        let result = analyser
            .analyse_satisfiable_task_from_context_with_registered_observer(
                task_id,
                &mut calc_context,
                &[OptimizedKPSetClassTestingItem::new()],
                229,
                Some(&mut observer_registry),
            )
            .expect("task-context analyser result");

        assert_eq!(result.corrected_individual.node, root);
        assert!(result.output.delivered_to_observer);
        let observer = observer_registry
            .get_observer(observer_handle)
            .expect("registered observer");
        assert_eq!(observer.get_told_messages().len(), 1);
        assert_eq!(observer.get_told_messages()[0].0, 223);
        assert_eq!(observer.get_told_messages()[0].2, 229);
        assert_eq!(
            observer.get_told_messages()[0].1.message_types(),
            vec![ClassificationMessageDataType::TellClassSubsumption]
        );
    }

    #[test]
    fn classification_message_analyser_task_context_entry_rejects_missing_adapter() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut calc_context = CalculationAlgorithmContext::new();
        let mut task = SatisfiableCalculationTask::new();
        task.set_processing_data_box_state(ProcessingDataBox::new());
        let task_id = calc_context.alloc_sat_calc_task(task);
        let no_observer: Option<&mut RecordingClassificationMessageDataObserver> = None;

        assert!(analyser
            .analyse_satisfiable_task_from_context(task_id, &mut calc_context, &[], 0, no_observer,)
            .is_none());
    }

    #[test]
    fn classification_message_analyser_classifier_references_release_without_required_info() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let mut node_vector = IndividualProcessNodeVector::new();
        let mut concepts = Arena::new();
        let mut ontology = OntologyArenas::new();
        let testing = concepts.push(concept_with_tag(CCATOM, 10, true));
        assert_eq!(
            ontology.alloc_concept(concept_with_tag(CCATOM, 10, true)),
            testing
        );
        let other_analyse = concepts.push(concept_with_tag(CCATOM, 30, true));
        assert_eq!(
            ontology.alloc_concept(concept_with_tag(CCATOM, 30, true)),
            other_analyse
        );
        let mut roles = Arena::new();
        let role = roles.push(role_with_tag(5, false));

        let root = add_identified_node(&mut process_context, 1);
        let other = add_identified_node(&mut process_context, 2);
        process_context
            .node_mut(root)
            .set_individual_ancestor_depth(0);
        process_context
            .node_mut(other)
            .set_individual_ancestor_depth(1);
        node_vector.set_data(1, root).set_data(2, other);

        let other_label_set = process_context.alloc_label_set(ReapplyConceptLabelSet::new(0));
        process_context
            .node_mut(other)
            .set_reapply_concept_label_set(other_label_set);
        let ancestor_track = add_dependency_track_point(
            &mut process_context,
            DepKind::Some,
            root,
            TrackPointId::NONE,
        );
        add_label_descriptor(
            &mut process_context,
            other_label_set,
            &concepts,
            other_analyse,
            false,
            ancestor_track,
        );
        add_role_link(&mut process_context, root, other, role, ancestor_track);

        let adapter = SatisfiableTaskClassificationMessageAdapter::new_with_handles(
            testing,
            71,
            73,
            std::collections::HashMap::new(),
            EFEXTRACTPOSSIBLESUBSUMERSOTHERNODES | EFEXTRACTOTHERNODESSINGLEDEPENDENCY,
        );
        let concept_process_datas = Arena::<ConceptProcessData>::new();
        let concept_reference_linking_datas = Arena::<ConceptSaturationReferenceLinkingData>::new();
        let testing_items = vec![OptimizedKPSetClassTestingItem::new()];
        let mut observer = RecordingClassificationMessageDataObserver::new();

        let result = analyser
            .analyse_satisfiable_task_classification_messages_with_classifier_references(
                &adapter,
                &process_context,
                &ontology,
                root,
                &node_vector,
                0,
                &std::collections::HashMap::new(),
                &std::collections::HashMap::new(),
                &[other],
                &concepts,
                &concept_process_datas,
                &concept_reference_linking_datas,
                &testing_items,
                &roles,
                97,
                Some(&mut observer),
            )
            .expect("classifier-reference analyser result");

        assert_eq!(result.other_node_visit_count, 1);
        assert_eq!(
            result.output,
            ClassificationAnalyserMessageOutputResult {
                had_message_data: false,
                delivered_to_observer: false,
                released_memory_pool: Some(97),
            }
        );
        assert!(observer.get_told_messages().is_empty());
    }

    #[test]
    fn classification_message_analyser_snapshots_possible_subsumption_state_from_classifier_item() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut concepts = Arena::new();
        let analysed = concepts.push(concept_with_tag(CCATOM, 30, true));
        let stale_low = concepts.push(concept_with_tag(CCATOM, 20, true));
        let stale_high = concepts.push(concept_with_tag(CCATOM, 40, true));
        let mut con_ref_hash = std::collections::HashMap::new();
        con_ref_hash.insert(analysed, 0);
        let adapter = SatisfiableTaskClassificationMessageAdapter::new_with_handles(
            ConceptId::new(999),
            71,
            73,
            con_ref_hash,
            EFEXTRACTPOSSIBLESUBSUMERSROOTNODE,
        );
        let concept_process_datas = Arena::<ConceptProcessData>::new();
        let concept_reference_linking_datas = Arena::<ConceptSaturationReferenceLinkingData>::new();
        let mut testing_item = OptimizedKPSetClassTestingItem::new();
        testing_item.set_possible_subsumption_map_initialized(true);
        testing_item
            .get_possible_subsumption_map(true)
            .expect("possible map")
            .insert(
                stale_high,
                OptimizedKPSetClassPossibleSubsumptionData::new(
                    OptimizedKPSetClassTestingItemId::new(0),
                ),
            );
        testing_item
            .get_possible_subsumption_map(true)
            .expect("possible map")
            .insert(
                stale_low,
                OptimizedKPSetClassPossibleSubsumptionData::new(
                    OptimizedKPSetClassTestingItemId::new(0),
                ),
            );
        testing_item
            .get_possible_subsumption_map(true)
            .expect("possible map")
            .set_remaining_possible_subsumption_count(2);
        let testing_items = vec![testing_item];

        let state = analyser
            .possible_subsumption_state_for_concept_from_classifier_references(
                analysed,
                &concepts,
                &concept_process_datas,
                &concept_reference_linking_datas,
                &adapter,
                &testing_items,
            )
            .expect("possible-subsumption state");

        assert!(state.possible_subsumption_map_initialized);
        assert!(state.remaining_possible_subsumptions);
        assert_eq!(
            state.possible_subsumption_concepts,
            vec![stale_low, stale_high]
        );
    }

    #[test]
    fn classification_message_analyser_classifier_state_wrapper_derives_possible_update() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let mut node_vector = IndividualProcessNodeVector::new();
        let mut concepts = Arena::new();
        let mut ontology = OntologyArenas::new();
        let testing = concepts.push(concept_with_tag(CCATOM, 10, true));
        assert_eq!(
            ontology.alloc_concept(concept_with_tag(CCATOM, 10, true)),
            testing
        );
        let root_possible = concepts.push(concept_with_tag(CCATOM, 20, true));
        assert_eq!(
            ontology.alloc_concept(concept_with_tag(CCATOM, 20, true)),
            root_possible
        );
        let stale_possible = concepts.push(concept_with_tag(CCATOM, 30, true));
        assert_eq!(
            ontology.alloc_concept(concept_with_tag(CCATOM, 30, true)),
            stale_possible
        );
        let roles = Arena::new();

        let root = add_identified_node(&mut process_context, 1);
        node_vector.set_data(1, root);
        let root_label_set = process_context.alloc_label_set(ReapplyConceptLabelSet::new(0));
        process_context
            .node_mut(root)
            .set_reapply_concept_label_set(root_label_set);
        let root_track = add_dependency_track_point(
            &mut process_context,
            DepKind::And,
            root,
            TrackPointId::NONE,
        );
        add_label_descriptor(
            &mut process_context,
            root_label_set,
            &concepts,
            root_possible,
            false,
            root_track,
        );

        let mut con_ref_hash = std::collections::HashMap::new();
        con_ref_hash.insert(root_possible, 0);
        let adapter = SatisfiableTaskClassificationMessageAdapter::new_with_handles(
            testing,
            71,
            73,
            con_ref_hash,
            EFEXTRACTPOSSIBLESUBSUMERSROOTNODE,
        );
        let concept_process_datas = Arena::<ConceptProcessData>::new();
        let concept_reference_linking_datas = Arena::<ConceptSaturationReferenceLinkingData>::new();
        let mut testing_item = OptimizedKPSetClassTestingItem::new();
        testing_item.set_possible_subsumption_map_initialized(true);
        testing_item
            .get_possible_subsumption_map(true)
            .expect("possible map")
            .insert(
                stale_possible,
                OptimizedKPSetClassPossibleSubsumptionData::new(
                    OptimizedKPSetClassTestingItemId::new(0),
                ),
            );
        testing_item
            .get_possible_subsumption_map(true)
            .expect("possible map")
            .set_remaining_possible_subsumption_count(1);
        let testing_items = vec![testing_item];
        let mut observer = RecordingClassificationMessageDataObserver::new();

        let result = analyser
            .analyse_satisfiable_task_classification_messages_with_classifier_state(
                &adapter,
                &process_context,
                &ontology,
                root,
                &node_vector,
                0,
                &std::collections::HashMap::new(),
                &[],
                &concepts,
                &concept_process_datas,
                &concept_reference_linking_datas,
                &testing_items,
                &roles,
                99,
                Some(&mut observer),
            )
            .expect("classifier-state analyser result");

        assert!(result.output.delivered_to_observer);
        assert_eq!(observer.get_told_messages().len(), 1);
        assert_eq!(
            observer.get_told_messages()[0].1.message_types(),
            vec![
                ClassificationMessageDataType::TellClassUpdatePossibleSubsumption,
                ClassificationMessageDataType::TellClassSubsumption,
            ]
        );
    }

    #[test]
    fn classification_message_analyser_resolves_saturated_individual_node_for_concept() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let positive_sat_node =
            process_context.alloc_sat_node(IndividualSaturationProcessNode::new(11));
        let negative_sat_node =
            process_context.alloc_sat_node(IndividualSaturationProcessNode::new(13));

        let mut concepts = Arena::new();
        let mut concept_process_datas = Arena::<ConceptProcessData>::new();
        let mut concept_reference_linking_datas =
            Arena::<ConceptSaturationReferenceLinkingData>::new();
        let mut saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();

        let positive_ref = {
            let mut linking = SaturationConceptReferenceLinking::new();
            linking.set_individual_process_node_for_concept(positive_sat_node);
            saturation_reference_linkings.push(linking)
        };
        let negative_ref = {
            let mut linking = SaturationConceptReferenceLinking::new();
            linking.set_individual_process_node_for_concept(negative_sat_node);
            saturation_reference_linkings.push(linking)
        };
        let con_ref = {
            let mut data = ConceptSaturationReferenceLinkingData::new();
            data.set_saturation_reference_linking_data(positive_ref, false)
                .set_saturation_reference_linking_data(negative_ref, true);
            concept_reference_linking_datas.push(data)
        };
        let con_proc = {
            let mut data = ConceptProcessData::new();
            data.set_concept_reference_linking(con_ref)
                .set_invalidated_reference_linking(true);
            concept_process_datas.push(data)
        };
        let mut concept_data = concept_with_tag(CCATOM, 31, true);
        concept_data.set_concept_data(con_proc.raw);
        let concept = concepts.push(concept_data);

        assert_eq!(
            analyser.get_saturated_individual_node_for_concept(
                concept,
                false,
                &concepts,
                &concept_process_datas,
                &concept_reference_linking_datas,
                &saturation_reference_linkings,
                &process_context,
            ),
            Some(positive_sat_node)
        );
        assert_eq!(
            analyser.get_saturated_individual_node_for_concept(
                concept,
                true,
                &concepts,
                &concept_process_datas,
                &concept_reference_linking_datas,
                &saturation_reference_linkings,
                &process_context,
            ),
            Some(negative_sat_node)
        );
    }

    #[test]
    fn classification_message_analyser_saturated_node_lookup_returns_none_for_missing_chain() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let process_context = ProcessContext::new();
        let mut concepts = Arena::new();
        let concept_without_data = concepts.push(concept_with_tag(CCATOM, 31, true));
        let mut concept_with_missing_ref = concept_with_tag(CCATOM, 41, true);
        concept_with_missing_ref.set_concept_data(0);
        let concept_with_missing_ref = concepts.push(concept_with_missing_ref);
        let concept_process_datas = Arena::<ConceptProcessData>::new();
        let concept_reference_linking_datas = Arena::<ConceptSaturationReferenceLinkingData>::new();
        let saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();

        assert_eq!(
            analyser.get_saturated_individual_node_for_concept(
                concept_without_data,
                false,
                &concepts,
                &concept_process_datas,
                &concept_reference_linking_datas,
                &saturation_reference_linkings,
                &process_context,
            ),
            None
        );
        assert_eq!(
            analyser.get_saturated_individual_node_for_concept(
                concept_with_missing_ref,
                false,
                &concepts,
                &concept_process_datas,
                &concept_reference_linking_datas,
                &saturation_reference_linkings,
                &process_context,
            ),
            None
        );
    }

    #[test]
    fn classification_message_analyser_resolves_direct_existential_saturated_successor_node() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let sat_node = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(11));
        let mut concepts = Arena::new();
        let concept = concepts.push(concept_with_tag(CCSOME, 31, true));
        let mut concept_process_datas = Arena::<ConceptProcessData>::new();
        let mut concept_reference_linking_datas =
            Arena::<ConceptSaturationReferenceLinkingData>::new();
        let mut saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let sat_ref = add_saturation_reference(&mut saturation_reference_linkings, sat_node);
        let mut ref_data = ConceptSaturationReferenceLinkingData::new();
        ref_data.set_existential_successor_concept_saturation_reference_linking_data(sat_ref);
        attach_concept_reference_data(
            &mut concepts,
            concept,
            &mut concept_process_datas,
            &mut concept_reference_linking_datas,
            ref_data,
        );

        assert_eq!(
            analyser.get_existential_saturated_individual_node_for_concept(
                concept,
                &concepts,
                &concept_process_datas,
                &concept_reference_linking_datas,
                &saturation_reference_linkings,
                &process_context,
                None,
            ),
            Some(sat_node)
        );
    }

    #[test]
    fn classification_message_analyser_existential_saturated_successor_falls_back_to_single_operand(
    ) {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let sat_node = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(11));
        let mut concepts = Arena::new();
        let operand = concepts.push(concept_with_tag(CCATOM, 41, true));
        let mut existential = concept_with_tag(CCSOME, 31, true);
        existential.add_operand_linker(operand, true);
        let existential = concepts.push(existential);
        let mut concept_process_datas = Arena::<ConceptProcessData>::new();
        let mut concept_reference_linking_datas =
            Arena::<ConceptSaturationReferenceLinkingData>::new();
        let mut saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let sat_ref = add_saturation_reference(&mut saturation_reference_linkings, sat_node);
        let mut ref_data = ConceptSaturationReferenceLinkingData::new();
        ref_data.set_saturation_reference_linking_data(sat_ref, true);
        attach_concept_reference_data(
            &mut concepts,
            operand,
            &mut concept_process_datas,
            &mut concept_reference_linking_datas,
            ref_data,
        );

        assert_eq!(
            analyser.get_existential_saturated_individual_node_for_concept(
                existential,
                &concepts,
                &concept_process_datas,
                &concept_reference_linking_datas,
                &saturation_reference_linkings,
                &process_context,
                None,
            ),
            Some(sat_node)
        );
    }

    #[test]
    fn classification_message_analyser_existential_saturated_successor_flips_single_all_operand() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let sat_node = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(11));
        let mut concepts = Arena::new();
        let operand = concepts.push(concept_with_tag(CCATOM, 41, true));
        let mut all_concept = concept_with_tag(CCALL, 31, true);
        all_concept.add_operand_linker(operand, false);
        let all_concept = concepts.push(all_concept);
        let mut concept_process_datas = Arena::<ConceptProcessData>::new();
        let mut concept_reference_linking_datas =
            Arena::<ConceptSaturationReferenceLinkingData>::new();
        let mut saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let sat_ref = add_saturation_reference(&mut saturation_reference_linkings, sat_node);
        let mut ref_data = ConceptSaturationReferenceLinkingData::new();
        ref_data.set_saturation_reference_linking_data(sat_ref, true);
        attach_concept_reference_data(
            &mut concepts,
            operand,
            &mut concept_process_datas,
            &mut concept_reference_linking_datas,
            ref_data,
        );

        assert_eq!(
            analyser.get_existential_saturated_individual_node_for_concept(
                all_concept,
                &concepts,
                &concept_process_datas,
                &concept_reference_linking_datas,
                &saturation_reference_linkings,
                &process_context,
                None,
            ),
            Some(sat_node)
        );
    }

    #[test]
    fn classification_message_analyser_existential_saturated_successor_falls_back_to_top_for_empty_operand_list(
    ) {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let sat_node = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(11));
        let mut concepts = Arena::new();
        let top = concepts.push(concept_with_tag(CCTOP, 1, true));
        let existential = concepts.push(concept_with_tag(CCSOME, 31, true));
        let mut concept_process_datas = Arena::<ConceptProcessData>::new();
        let mut concept_reference_linking_datas =
            Arena::<ConceptSaturationReferenceLinkingData>::new();
        let mut saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let sat_ref = add_saturation_reference(&mut saturation_reference_linkings, sat_node);
        let mut ref_data = ConceptSaturationReferenceLinkingData::new();
        ref_data.set_saturation_reference_linking_data(sat_ref, false);
        attach_concept_reference_data(
            &mut concepts,
            top,
            &mut concept_process_datas,
            &mut concept_reference_linking_datas,
            ref_data,
        );

        assert_eq!(
            analyser.get_existential_saturated_individual_node_for_concept(
                existential,
                &concepts,
                &concept_process_datas,
                &concept_reference_linking_datas,
                &saturation_reference_linkings,
                &process_context,
                Some(top),
            ),
            Some(sat_node)
        );
    }

    #[test]
    fn classification_message_analyser_existential_saturated_successor_returns_none_for_multi_operand_fallback(
    ) {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let process_context = ProcessContext::new();
        let mut concepts = Arena::new();
        let op1 = concepts.push(concept_with_tag(CCATOM, 41, true));
        let op2 = concepts.push(concept_with_tag(CCATOM, 43, true));
        let mut existential = concept_with_tag(CCSOME, 31, true);
        existential.add_operand_linker(op1, false);
        existential.add_operand_linker(op2, false);
        let existential = concepts.push(existential);
        let concept_process_datas = Arena::<ConceptProcessData>::new();
        let concept_reference_linking_datas = Arena::<ConceptSaturationReferenceLinkingData>::new();
        let saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();

        assert_eq!(
            analyser.get_existential_saturated_individual_node_for_concept(
                existential,
                &concepts,
                &concept_process_datas,
                &concept_reference_linking_datas,
                &saturation_reference_linkings,
                &process_context,
                None,
            ),
            None
        );
    }

    #[test]
    fn classification_message_analyser_trivial_propagation_collects_negated_sub() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut concepts = Arena::new();
        let sub = concepts.push(concept_with_tag(CCSUB, 31, true));
        let mut trivial = Vec::new();

        assert!(analyser.collect_trivial_propagation_testing_concepts(
            sub,
            true,
            &concepts,
            &mut trivial,
        ));
        assert_eq!(trivial, vec![(sub, true)]);
    }

    #[test]
    fn classification_message_analyser_trivial_propagation_collects_positive_all_family() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut concepts = Arena::new();
        let all = concepts.push(concept_with_tag(CCALL, 31, true));
        let impl_all = concepts.push(concept_with_tag(CCIMPLALL, 33, true));
        let branch_aq_all = concepts.push(concept_with_tag(CCBRANCHAQALL, 35, true));
        let mut trivial = Vec::new();

        assert!(analyser.collect_trivial_propagation_testing_concepts(
            all,
            false,
            &concepts,
            &mut trivial,
        ));
        assert!(analyser.collect_trivial_propagation_testing_concepts(
            impl_all,
            false,
            &concepts,
            &mut trivial,
        ));
        assert!(analyser.collect_trivial_propagation_testing_concepts(
            branch_aq_all,
            false,
            &concepts,
            &mut trivial,
        ));
        assert_eq!(
            trivial,
            vec![(all, false), (impl_all, false), (branch_aq_all, false)]
        );
    }

    #[test]
    fn classification_message_analyser_trivial_propagation_recurses_positive_aqand_family() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut concepts = Arena::new();
        let sub = concepts.push(concept_with_tag(CCSUB, 31, true));
        let all = concepts.push(concept_with_tag(CCALL, 33, true));
        let mut aqand = concept_with_tag(CCAQAND, 35, true);
        aqand.add_operand_linker(sub, true);
        aqand.add_operand_linker(all, false);
        let aqand = concepts.push(aqand);
        let mut trivial = Vec::new();

        assert!(analyser.collect_trivial_propagation_testing_concepts(
            aqand,
            false,
            &concepts,
            &mut trivial,
        ));
        assert_eq!(trivial, vec![(sub, true), (all, false)]);
    }

    #[test]
    fn classification_message_analyser_trivial_propagation_rejects_non_trivial_operand() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut concepts = Arena::new();
        let atom = concepts.push(concept_with_tag(CCATOM, 31, true));
        let mut aqand = concept_with_tag(CCIMPLAQAND, 35, true);
        aqand.add_operand_linker(atom, false);
        let aqand = concepts.push(aqand);
        let mut trivial = Vec::new();

        assert!(!analyser.collect_trivial_propagation_testing_concepts(
            aqand,
            false,
            &concepts,
            &mut trivial,
        ));
        assert!(trivial.is_empty());
        assert!(!analyser.collect_trivial_propagation_testing_concepts(
            atom,
            false,
            &concepts,
            &mut trivial,
        ));
    }

    #[test]
    fn classification_message_analyser_automate_transaction_collects_saturated_operand_for_matching_role(
    ) {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let sat_node = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(11));
        process_context.sat_node_mut(sat_node).set_completed(true);
        let mut concepts = Arena::new();
        let mut concept_process_datas = Arena::<ConceptProcessData>::new();
        let mut concept_reference_linking_datas =
            Arena::<ConceptSaturationReferenceLinkingData>::new();
        let mut saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let role = RoleId::new(7);
        let operand = concepts.push(concept_with_tag(CCATOM, 31, true));
        let sat_ref = add_saturation_reference(&mut saturation_reference_linkings, sat_node);
        let mut ref_data = ConceptSaturationReferenceLinkingData::new();
        ref_data.set_saturation_reference_linking_data(sat_ref, false);
        attach_concept_reference_data(
            &mut concepts,
            operand,
            &mut concept_process_datas,
            &mut concept_reference_linking_datas,
            ref_data,
        );
        let mut aqall = concept_with_tag(CCAQALL, 41, true);
        aqall.set_role(role);
        aqall.add_operand_linker(operand, false);
        let aqall = concepts.push(aqall);
        let mut successors = Vec::new();
        let mut trivial = Vec::new();

        assert!(analyser.add_automate_transaction_concepts(
            aqall,
            false,
            role,
            &concepts,
            &concept_process_datas,
            &concept_reference_linking_datas,
            &saturation_reference_linkings,
            &process_context,
            &mut successors,
            &mut trivial,
        ));
        assert_eq!(successors, vec![sat_node]);
        assert!(trivial.is_empty());
    }

    #[test]
    fn classification_message_analyser_automate_transaction_rejects_problematic_saturated_operand()
    {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let sat_node = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(11));
        process_context.sat_node_mut(sat_node).set_completed(true);
        process_context
            .sat_node_mut(sat_node)
            .indirect_status_flags
            .add_flags_code(IndividualSaturationProcessNodeStatusFlags::INDSATFLAGCLASHED);
        let mut concepts = Arena::new();
        let mut concept_process_datas = Arena::<ConceptProcessData>::new();
        let mut concept_reference_linking_datas =
            Arena::<ConceptSaturationReferenceLinkingData>::new();
        let mut saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let role = RoleId::new(7);
        let operand = concepts.push(concept_with_tag(CCATOM, 31, true));
        let sat_ref = add_saturation_reference(&mut saturation_reference_linkings, sat_node);
        let mut ref_data = ConceptSaturationReferenceLinkingData::new();
        ref_data.set_saturation_reference_linking_data(sat_ref, false);
        attach_concept_reference_data(
            &mut concepts,
            operand,
            &mut concept_process_datas,
            &mut concept_reference_linking_datas,
            ref_data,
        );
        let mut aqall = concept_with_tag(CCIMPLAQALL, 41, true);
        aqall.set_role(role);
        aqall.add_operand_linker(operand, false);
        let aqall = concepts.push(aqall);
        let mut successors = Vec::new();
        let mut trivial = Vec::new();

        assert!(!analyser.add_automate_transaction_concepts(
            aqall,
            false,
            role,
            &concepts,
            &concept_process_datas,
            &concept_reference_linking_datas,
            &saturation_reference_linkings,
            &process_context,
            &mut successors,
            &mut trivial,
        ));
        assert!(successors.is_empty());
        assert!(trivial.is_empty());
    }

    #[test]
    fn classification_message_analyser_automate_transaction_falls_back_to_trivial_operand() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let process_context = ProcessContext::new();
        let mut concepts = Arena::new();
        let concept_process_datas = Arena::<ConceptProcessData>::new();
        let concept_reference_linking_datas = Arena::<ConceptSaturationReferenceLinkingData>::new();
        let saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let role = RoleId::new(7);
        let sub = concepts.push(concept_with_tag(CCSUB, 31, true));
        let all = concepts.push(concept_with_tag(CCALL, 33, true));
        let mut aqall = concept_with_tag(CCBRANCHAQALL, 41, true);
        aqall.set_role(role);
        aqall.add_operand_linker(sub, true);
        aqall.add_operand_linker(all, false);
        let aqall = concepts.push(aqall);
        let mut successors = Vec::new();
        let mut trivial = Vec::new();

        assert!(analyser.add_automate_transaction_concepts(
            aqall,
            false,
            role,
            &concepts,
            &concept_process_datas,
            &concept_reference_linking_datas,
            &saturation_reference_linkings,
            &process_context,
            &mut successors,
            &mut trivial,
        ));
        assert!(successors.is_empty());
        assert_eq!(trivial, vec![(sub, true), (all, false)]);
    }

    #[test]
    fn classification_message_analyser_automate_transaction_rejects_non_trivial_unsaturated_operand(
    ) {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let process_context = ProcessContext::new();
        let mut concepts = Arena::new();
        let concept_process_datas = Arena::<ConceptProcessData>::new();
        let concept_reference_linking_datas = Arena::<ConceptSaturationReferenceLinkingData>::new();
        let saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let role = RoleId::new(7);
        let atom = concepts.push(concept_with_tag(CCATOM, 31, true));
        let mut aqall = concept_with_tag(CCAQALL, 41, true);
        aqall.set_role(role);
        aqall.add_operand_linker(atom, false);
        let aqall = concepts.push(aqall);
        let mut successors = Vec::new();
        let mut trivial = Vec::new();

        assert!(!analyser.add_automate_transaction_concepts(
            aqall,
            false,
            role,
            &concepts,
            &concept_process_datas,
            &concept_reference_linking_datas,
            &saturation_reference_linkings,
            &process_context,
            &mut successors,
            &mut trivial,
        ));
        assert!(successors.is_empty());
        assert!(trivial.is_empty());
    }

    #[test]
    fn classification_message_analyser_automate_transaction_recurses_positive_aqand_family() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let sat_node = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(11));
        process_context.sat_node_mut(sat_node).set_completed(true);
        let mut concepts = Arena::new();
        let mut concept_process_datas = Arena::<ConceptProcessData>::new();
        let mut concept_reference_linking_datas =
            Arena::<ConceptSaturationReferenceLinkingData>::new();
        let mut saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let role = RoleId::new(7);
        let operand = concepts.push(concept_with_tag(CCATOM, 31, true));
        let sat_ref = add_saturation_reference(&mut saturation_reference_linkings, sat_node);
        let mut ref_data = ConceptSaturationReferenceLinkingData::new();
        ref_data.set_saturation_reference_linking_data(sat_ref, false);
        attach_concept_reference_data(
            &mut concepts,
            operand,
            &mut concept_process_datas,
            &mut concept_reference_linking_datas,
            ref_data,
        );
        let mut aqall = concept_with_tag(CCAQALL, 41, true);
        aqall.set_role(role);
        aqall.add_operand_linker(operand, false);
        let aqall = concepts.push(aqall);
        let trivial_sub = concepts.push(concept_with_tag(CCSUB, 43, true));
        let mut trivial_aqall = concept_with_tag(CCBRANCHAQALL, 45, true);
        trivial_aqall.set_role(role);
        trivial_aqall.add_operand_linker(trivial_sub, true);
        let trivial_aqall = concepts.push(trivial_aqall);
        let mut aqand = concept_with_tag(CCIMPLAQAND, 51, true);
        aqand.add_operand_linker(aqall, false);
        aqand.add_operand_linker(trivial_aqall, false);
        let aqand = concepts.push(aqand);
        let mut successors = Vec::new();
        let mut trivial = Vec::new();

        assert!(analyser.add_automate_transaction_concepts(
            aqand,
            false,
            role,
            &concepts,
            &concept_process_datas,
            &concept_reference_linking_datas,
            &saturation_reference_linkings,
            &process_context,
            &mut successors,
            &mut trivial,
        ));
        assert_eq!(successors, vec![sat_node]);
        assert_eq!(trivial, vec![(trivial_sub, true)]);
    }

    #[test]
    fn classification_message_analyser_automate_transaction_ignores_non_matching_role() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let process_context = ProcessContext::new();
        let mut concepts = Arena::new();
        let concept_process_datas = Arena::<ConceptProcessData>::new();
        let concept_reference_linking_datas = Arena::<ConceptSaturationReferenceLinkingData>::new();
        let saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let atom = concepts.push(concept_with_tag(CCATOM, 31, true));
        let mut aqall = concept_with_tag(CCAQALL, 41, true);
        aqall.set_role(RoleId::new(7));
        aqall.add_operand_linker(atom, false);
        let aqall = concepts.push(aqall);
        let mut successors = Vec::new();
        let mut trivial = Vec::new();

        assert!(analyser.add_automate_transaction_concepts(
            aqall,
            false,
            RoleId::new(9),
            &concepts,
            &concept_process_datas,
            &concept_reference_linking_datas,
            &saturation_reference_linkings,
            &process_context,
            &mut successors,
            &mut trivial,
        ));
        assert!(successors.is_empty());
        assert!(trivial.is_empty());
    }

    #[test]
    fn classification_message_analyser_collects_successor_merging_nodes_from_completion_reapply_queue(
    ) {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let (node, _) = add_completion_label_set_node(&mut process_context);
        let sat_node = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(11));
        process_context.sat_node_mut(sat_node).set_completed(true);
        let mut concepts = Arena::new();
        let mut roles = Arena::new();
        let mut concept_process_datas = Arena::<ConceptProcessData>::new();
        let mut concept_reference_linking_datas =
            Arena::<ConceptSaturationReferenceLinkingData>::new();
        let mut saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let super_role = roles.push(role_with_tag(3, false));
        let mut role_data = role_with_tag(7, false);
        role_data.add_indirect_super_role_linker(NegLink {
            target: super_role,
            negated: false,
        });
        let role = roles.push(role_data);
        let operand = concepts.push(concept_with_tag(CCATOM, 31, true));
        let sat_ref = add_saturation_reference(&mut saturation_reference_linkings, sat_node);
        let mut ref_data = ConceptSaturationReferenceLinkingData::new();
        ref_data.set_saturation_reference_linking_data(sat_ref, false);
        attach_concept_reference_data(
            &mut concepts,
            operand,
            &mut concept_process_datas,
            &mut concept_reference_linking_datas,
            ref_data,
        );
        let mut all = concept_with_tag(CCALL, 41, true);
        all.add_operand_linker(operand, false);
        let all = concepts.push(all);
        let mut con_des = ConceptDescriptor::new();
        con_des.concept = all;
        con_des.negated = false;
        let con_des = process_context.alloc_con_desc(con_des);
        let reapply = process_context.alloc_reapply_con_desc(ReapplyConceptDescriptor::new(
            con_des,
            TrackPointId::NONE,
            false,
        ));
        process_context.node_add_role_reapply_concept_descriptor(node, super_role, reapply);
        let mut successors = Vec::new();
        let mut trivial = Vec::new();
        let mut backward_roles = std::collections::HashSet::new();

        assert!(
            analyser.collect_successor_merging_nodes_and_concepts_for_completion_node(
                node,
                role,
                &concepts,
                &roles,
                &concept_process_datas,
                &concept_reference_linking_datas,
                &saturation_reference_linkings,
                &mut process_context,
                &mut successors,
                &mut trivial,
                &mut backward_roles,
            )
        );
        assert_eq!(successors, vec![sat_node]);
        assert!(trivial.is_empty());
        assert!(backward_roles.is_empty());
    }

    #[test]
    fn classification_message_analyser_collects_successor_merging_trivial_fallback_and_backward_roles(
    ) {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let (node, _) = add_completion_label_set_node(&mut process_context);
        let mut concepts = Arena::new();
        let mut roles = Arena::new();
        let concept_process_datas = Arena::<ConceptProcessData>::new();
        let concept_reference_linking_datas = Arena::<ConceptSaturationReferenceLinkingData>::new();
        let saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let super_role = roles.push(role_with_tag(3, false));
        let inverse_super_role = roles.push(role_with_tag(5, false));
        let mut role_data = role_with_tag(7, false);
        role_data.add_indirect_super_role_linker(NegLink {
            target: super_role,
            negated: false,
        });
        role_data.add_indirect_super_role_linker(NegLink {
            target: inverse_super_role,
            negated: true,
        });
        let role = roles.push(role_data);
        let sub = concepts.push(concept_with_tag(CCSUB, 31, true));
        let mut some = concept_with_tag(CCSOME, 41, true);
        some.add_operand_linker(sub, false);
        let some = concepts.push(some);
        let mut con_des = ConceptDescriptor::new();
        con_des.concept = some;
        con_des.negated = true;
        let con_des = process_context.alloc_con_desc(con_des);
        let reapply = process_context.alloc_reapply_con_desc(ReapplyConceptDescriptor::new(
            con_des,
            TrackPointId::NONE,
            false,
        ));
        process_context.node_add_role_reapply_concept_descriptor(node, super_role, reapply);
        let mut successors = Vec::new();
        let mut trivial = Vec::new();
        let mut backward_roles = std::collections::HashSet::new();

        assert!(
            analyser.collect_successor_merging_nodes_and_concepts_for_completion_node(
                node,
                role,
                &concepts,
                &roles,
                &concept_process_datas,
                &concept_reference_linking_datas,
                &saturation_reference_linkings,
                &mut process_context,
                &mut successors,
                &mut trivial,
                &mut backward_roles,
            )
        );
        assert!(successors.is_empty());
        assert_eq!(trivial, vec![(sub, true)]);
        assert!(backward_roles.contains(&inverse_super_role));
        assert_eq!(backward_roles.len(), 1);
    }

    #[test]
    fn classification_message_analyser_collect_successor_merging_rejects_unsupported_reapply_concept(
    ) {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let (node, _) = add_completion_label_set_node(&mut process_context);
        let mut concepts = Arena::new();
        let mut roles = Arena::new();
        let concept_process_datas = Arena::<ConceptProcessData>::new();
        let concept_reference_linking_datas = Arena::<ConceptSaturationReferenceLinkingData>::new();
        let saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let super_role = roles.push(role_with_tag(3, false));
        let mut role_data = role_with_tag(7, false);
        role_data.add_indirect_super_role_linker(NegLink {
            target: super_role,
            negated: false,
        });
        let role = roles.push(role_data);
        let atom = concepts.push(concept_with_tag(CCATOM, 31, true));
        let mut con_des = ConceptDescriptor::new();
        con_des.concept = atom;
        con_des.negated = false;
        let con_des = process_context.alloc_con_desc(con_des);
        let reapply = process_context.alloc_reapply_con_desc(ReapplyConceptDescriptor::new(
            con_des,
            TrackPointId::NONE,
            false,
        ));
        process_context.node_add_role_reapply_concept_descriptor(node, super_role, reapply);
        let mut successors = Vec::new();
        let mut trivial = Vec::new();
        let mut backward_roles = std::collections::HashSet::new();

        assert!(
            !analyser.collect_successor_merging_nodes_and_concepts_for_completion_node(
                node,
                role,
                &concepts,
                &roles,
                &concept_process_datas,
                &concept_reference_linking_datas,
                &saturation_reference_linkings,
                &mut process_context,
                &mut successors,
                &mut trivial,
                &mut backward_roles,
            )
        );
        assert!(successors.is_empty());
        assert!(trivial.is_empty());
        assert!(backward_roles.is_empty());
    }

    #[test]
    fn classification_message_analyser_recursive_successor_merging_collects_influence_for_self_super_role(
    ) {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let sat_node = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(11));
        process_context.sat_node_mut(sat_node).set_completed(true);
        let mut concepts = Arena::new();
        let mut roles = Arena::new();
        let mut concept_process_datas = Arena::<ConceptProcessData>::new();
        let mut concept_reference_linking_datas =
            Arena::<ConceptSaturationReferenceLinkingData>::new();
        let mut saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let role = roles.push(role_with_tag(7, false));
        roles.get_mut(role).add_indirect_super_role_linker(NegLink {
            target: role,
            negated: false,
        });
        let operand = concepts.push(concept_with_tag(CCATOM, 31, true));
        let sat_ref = add_saturation_reference(&mut saturation_reference_linkings, sat_node);
        let mut ref_data = ConceptSaturationReferenceLinkingData::new();
        ref_data.set_saturation_reference_linking_data(sat_ref, false);
        attach_concept_reference_data(
            &mut concepts,
            operand,
            &mut concept_process_datas,
            &mut concept_reference_linking_datas,
            ref_data,
        );
        let mut next_successors = Vec::new();
        let mut next_trivial = Vec::new();
        let mut next_backward_roles = std::collections::HashSet::new();

        assert!(
            analyser.collect_successor_merging_nodes_and_concepts_for_saturation_node(
                SatNodeId::NONE,
                role,
                &concepts,
                &roles,
                &concept_process_datas,
                &concept_reference_linking_datas,
                &saturation_reference_linkings,
                &process_context,
                &[],
                &mut next_successors,
                &mut next_trivial,
                &mut next_backward_roles,
                &[(role, (operand, false))],
            )
        );
        assert_eq!(next_successors, vec![sat_node]);
        assert!(next_trivial.is_empty());
        assert!(next_backward_roles.is_empty());
    }

    #[test]
    fn classification_message_analyser_recursive_successor_merging_preserves_influence_role_key_guard(
    ) {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let process_context = ProcessContext::new();
        let mut concepts = Arena::new();
        let mut roles = Arena::new();
        let concept_process_datas = Arena::<ConceptProcessData>::new();
        let concept_reference_linking_datas = Arena::<ConceptSaturationReferenceLinkingData>::new();
        let saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let super_role = roles.push(role_with_tag(3, false));
        let mut role_data = role_with_tag(7, false);
        role_data.add_indirect_super_role_linker(NegLink {
            target: super_role,
            negated: false,
        });
        let role = roles.push(role_data);
        let sub = concepts.push(concept_with_tag(CCSUB, 31, true));
        let mut next_successors = Vec::new();
        let mut next_trivial = Vec::new();
        let mut next_backward_roles = std::collections::HashSet::new();

        assert!(
            analyser.collect_successor_merging_nodes_and_concepts_for_saturation_node(
                SatNodeId::NONE,
                role,
                &concepts,
                &roles,
                &concept_process_datas,
                &concept_reference_linking_datas,
                &saturation_reference_linkings,
                &process_context,
                &[],
                &mut next_successors,
                &mut next_trivial,
                &mut next_backward_roles,
                &[(super_role, (sub, true))],
            )
        );
        assert!(next_successors.is_empty());
        assert!(next_trivial.is_empty());
        assert!(next_backward_roles.is_empty());
    }

    #[test]
    fn classification_message_analyser_recursive_successor_merging_collects_backward_reapply_trivial_and_null_successor(
    ) {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let succ_node = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(11));
        let mut concepts = Arena::new();
        let mut roles = Arena::new();
        let concept_process_datas = Arena::<ConceptProcessData>::new();
        let concept_reference_linking_datas = Arena::<ConceptSaturationReferenceLinkingData>::new();
        let saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let super_role = roles.push(role_with_tag(3, false));
        let mut role_data = role_with_tag(7, false);
        role_data.add_indirect_super_role_linker(NegLink {
            target: super_role,
            negated: false,
        });
        let role = roles.push(role_data);
        let sub = concepts.push(concept_with_tag(CCSUB, 31, true));
        let mut some = concept_with_tag(CCSOME, 41, true);
        some.add_operand_linker(sub, false);
        let some = concepts.push(some);
        let con_sat_des = add_saturation_concept_descriptor(&mut process_context, some, true);
        add_backward_reapply_for_role(&mut process_context, succ_node, super_role, con_sat_des);
        let mut next_successors = Vec::new();
        let mut next_trivial = Vec::new();
        let mut next_backward_roles = std::collections::HashSet::new();

        assert!(
            analyser.collect_successor_merging_nodes_and_concepts_for_saturation_node(
                SatNodeId::NONE,
                role,
                &concepts,
                &roles,
                &concept_process_datas,
                &concept_reference_linking_datas,
                &saturation_reference_linkings,
                &process_context,
                &[succ_node],
                &mut next_successors,
                &mut next_trivial,
                &mut next_backward_roles,
                &[],
            )
        );
        assert_eq!(next_successors, vec![SatNodeId::NONE]);
        assert_eq!(next_trivial, vec![(sub, true)]);
        assert!(next_backward_roles.is_empty());
    }

    #[test]
    fn classification_message_analyser_recursive_successor_merging_skips_excluded_substitute_and_records_inverse_role(
    ) {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let succ_node = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(11));
        let substitute_node =
            process_context.alloc_sat_node(IndividualSaturationProcessNode::new(13));
        process_context
            .sat_node_mut(succ_node)
            .set_substitute_individual_node(substitute_node);
        let mut concepts = Arena::new();
        let mut roles = Arena::new();
        let concept_process_datas = Arena::<ConceptProcessData>::new();
        let concept_reference_linking_datas = Arena::<ConceptSaturationReferenceLinkingData>::new();
        let saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let super_role = roles.push(role_with_tag(3, false));
        let inverse_super_role = roles.push(role_with_tag(5, false));
        let mut role_data = role_with_tag(7, false);
        role_data.add_indirect_super_role_linker(NegLink {
            target: super_role,
            negated: false,
        });
        role_data.add_indirect_super_role_linker(NegLink {
            target: inverse_super_role,
            negated: true,
        });
        let role = roles.push(role_data);
        let atom = concepts.push(concept_with_tag(CCATOM, 31, true));
        let con_sat_des = add_saturation_concept_descriptor(&mut process_context, atom, false);
        add_backward_reapply_for_role(
            &mut process_context,
            substitute_node,
            super_role,
            con_sat_des,
        );
        let mut next_successors = Vec::new();
        let mut next_trivial = Vec::new();
        let mut next_backward_roles = std::collections::HashSet::new();

        assert!(
            analyser.collect_successor_merging_nodes_and_concepts_for_saturation_node(
                substitute_node,
                role,
                &concepts,
                &roles,
                &concept_process_datas,
                &concept_reference_linking_datas,
                &saturation_reference_linkings,
                &process_context,
                &[succ_node],
                &mut next_successors,
                &mut next_trivial,
                &mut next_backward_roles,
                &[],
            )
        );
        assert!(next_successors.is_empty());
        assert!(next_trivial.is_empty());
        assert!(next_backward_roles.contains(&inverse_super_role));
        assert_eq!(next_backward_roles.len(), 1);
    }

    #[test]
    fn classification_message_analyser_recursive_successor_merging_rejects_unsupported_backward_reapply(
    ) {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let succ_node = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(11));
        let mut concepts = Arena::new();
        let mut roles = Arena::new();
        let concept_process_datas = Arena::<ConceptProcessData>::new();
        let concept_reference_linking_datas = Arena::<ConceptSaturationReferenceLinkingData>::new();
        let saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let super_role = roles.push(role_with_tag(3, false));
        let mut role_data = role_with_tag(7, false);
        role_data.add_indirect_super_role_linker(NegLink {
            target: super_role,
            negated: false,
        });
        let role = roles.push(role_data);
        let atom = concepts.push(concept_with_tag(CCATOM, 31, true));
        let con_sat_des = add_saturation_concept_descriptor(&mut process_context, atom, false);
        add_backward_reapply_for_role(&mut process_context, succ_node, super_role, con_sat_des);
        let mut next_successors = Vec::new();
        let mut next_trivial = Vec::new();
        let mut next_backward_roles = std::collections::HashSet::new();

        assert!(
            !analyser.collect_successor_merging_nodes_and_concepts_for_saturation_node(
                SatNodeId::NONE,
                role,
                &concepts,
                &roles,
                &concept_process_datas,
                &concept_reference_linking_datas,
                &saturation_reference_linkings,
                &process_context,
                &[succ_node],
                &mut next_successors,
                &mut next_trivial,
                &mut next_backward_roles,
                &[],
            )
        );
        assert!(next_successors.is_empty());
        assert!(next_trivial.is_empty());
        assert!(next_backward_roles.is_empty());
    }

    #[test]
    fn classification_message_analyser_multiple_successor_trigger_prep_collects_sub_triggers_and_all_influences(
    ) {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let process_context = ProcessContext::new();
        let mut concepts = Arena::new();
        let role = RoleId::new(7);
        let sub = concepts.push(concept_with_tag(CCSUB, 31, true));
        let operand = concepts.push(concept_with_tag(CCATOM, 33, true));
        let mut all = concept_with_tag(CCALL, 41, true);
        all.set_role(role);
        all.add_operand_linker(operand, true);
        let all = concepts.push(all);
        let backward_roles = std::collections::HashSet::new();

        let (trigger_hash, influence) = analyser
            .prepare_multiple_saturated_successor_merge_triggers(
                SatNodeId::NONE,
                &[],
                &[(sub, true), (all, false)],
                &backward_roles,
                &concepts,
                &process_context,
            )
            .expect("trigger prep succeeds");

        let trigger = trigger_hash
            .get(&concepts.get(sub).get_concept_tag())
            .expect("sub trigger");
        assert!(!trigger.trigger_flag);
        assert!(trigger.negation_flag);
        assert_eq!(trigger.concept, sub);
        assert_eq!(trigger.indi_sat_node, SatNodeId::NONE);
        assert_eq!(influence, vec![(role, (operand, true))]);
    }

    #[test]
    fn classification_message_analyser_multiple_successor_trigger_prep_rejects_backward_role_link()
    {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let existential = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(11));
        let successor = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(13));
        let source = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(17));
        let role = RoleId::new(7);
        process_context.sat_node_add_backward_propagation_link(successor, role, source);
        let concepts = Arena::<Concept>::new();
        let mut backward_roles = std::collections::HashSet::new();
        backward_roles.insert(role);

        assert!(analyser
            .prepare_multiple_saturated_successor_merge_triggers(
                existential,
                &[successor],
                &[],
                &backward_roles,
                &concepts,
                &process_context,
            )
            .is_none());
    }

    #[test]
    fn classification_message_analyser_multiple_successor_trigger_prep_ignores_positive_sub_and_rejects_all_with_backward_role(
    ) {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let process_context = ProcessContext::new();
        let mut concepts = Arena::new();
        let sub = concepts.push(concept_with_tag(CCSUB, 31, true));
        let backward_roles = std::collections::HashSet::new();

        let (trigger_hash, influence) = analyser
            .prepare_multiple_saturated_successor_merge_triggers(
                SatNodeId::NONE,
                &[],
                &[(sub, true), (sub, false)],
                &backward_roles,
                &concepts,
                &process_context,
            )
            .expect("positive CCSUB is ignored by this C++ block");
        assert_eq!(trigger_hash.len(), 1);
        assert!(influence.is_empty());

        let mut all = concept_with_tag(CCALL, 41, true);
        all.set_role(RoleId::new(7));
        all.add_operand_linker(sub, false);
        let all = concepts.push(all);
        let mut blocked_roles = std::collections::HashSet::new();
        blocked_roles.insert(RoleId::new(7));
        assert!(analyser
            .prepare_multiple_saturated_successor_merge_triggers(
                SatNodeId::NONE,
                &[],
                &[(all, false)],
                &blocked_roles,
                &concepts,
                &process_context,
            )
            .is_none());
    }

    #[test]
    fn classification_message_analyser_multiple_successor_label_trigger_merge_records_saturation_descriptor(
    ) {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let mut concepts = Arena::new();
        let concept = concepts.push(concept_with_tag(CCATOM, 31, true));
        let (sat_node, sat_label_set) = add_saturation_label_set_node(&mut process_context);
        add_saturation_label_descriptor(
            &mut process_context,
            sat_label_set,
            &concepts,
            concept,
            true,
            INVALID,
        );
        let mut trigger_hash = std::collections::HashMap::new();

        assert!(analyser.merge_successor_saturation_label_triggers(
            &[sat_node],
            &concepts,
            &process_context,
            &mut trigger_hash,
        ));
        let trigger = trigger_hash
            .get(&concepts.get(concept).get_concept_tag())
            .expect("merged trigger");
        assert!(!trigger.trigger_flag);
        assert!(trigger.negation_flag);
        assert_eq!(trigger.concept, concept);
        assert_eq!(trigger.indi_sat_node, sat_node);
    }

    #[test]
    fn classification_message_analyser_multiple_successor_label_trigger_merge_rejects_polarity_conflict(
    ) {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let mut concepts = Arena::new();
        let concept = concepts.push(concept_with_tag(CCATOM, 31, true));
        let (sat_node, sat_label_set) = add_saturation_label_set_node(&mut process_context);
        add_saturation_label_descriptor(
            &mut process_context,
            sat_label_set,
            &concepts,
            concept,
            false,
            INVALID,
        );
        let mut trigger_hash = std::collections::HashMap::new();
        trigger_hash.insert(
            concepts.get(concept).get_concept_tag(),
            ConceptNegationTriggerItem {
                concept,
                negation_flag: true,
                ..Default::default()
            },
        );

        assert!(!analyser.merge_successor_saturation_label_triggers(
            &[sat_node],
            &concepts,
            &process_context,
            &mut trigger_hash,
        ));
    }

    #[test]
    fn classification_message_analyser_multiple_successor_label_trigger_merge_handles_implication_trigger_conflicts(
    ) {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let mut concepts = Arena::new();
        let concept = concepts.push(concept_with_tag(CCATOM, 31, true));
        let (sat_node, sat_label_set) = add_saturation_label_set_node(&mut process_context);
        process_context
            .reapply_con_sat_label_set_mut(sat_label_set)
            .concept_des_dep_hash
            .insert(
                concepts.get(concept).get_concept_tag(),
                ConceptSaturationDescriptorReapplyData {
                    con_sat_des: super::super::super::saturation::satellites::ConceptSaturationDescriptorId::NONE,
                    imp_reapply_con_sat_des: super::super::super::saturation::satellites::ImplicationReapplyConceptSaturationDescriptorId::new(77),
                },
            );
        let mut trigger_hash = std::collections::HashMap::new();

        assert!(analyser.merge_successor_saturation_label_triggers(
            &[sat_node],
            &concepts,
            &process_context,
            &mut trigger_hash,
        ));
        assert!(
            trigger_hash
                .get(&concepts.get(concept).get_concept_tag())
                .expect("imp trigger")
                .trigger_flag
        );

        trigger_hash.insert(
            concepts.get(concept).get_concept_tag(),
            ConceptNegationTriggerItem {
                concept,
                negation_flag: false,
                ..Default::default()
            },
        );
        assert!(!analyser.merge_successor_saturation_label_triggers(
            &[sat_node],
            &concepts,
            &process_context,
            &mut trigger_hash,
        ));
    }

    #[test]
    fn classification_message_analyser_multiple_successor_label_trigger_merge_follows_substitute_node(
    ) {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let mut concepts = Arena::new();
        let reference = concepts.push(concept_with_tag(CCATOM, 29, true));
        let concept = concepts.push(concept_with_tag(CCATOM, 31, true));
        let original = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(11));
        let (substitute, sat_label_set) = add_saturation_label_set_node(&mut process_context);
        process_context
            .sat_node_mut(original)
            .set_substitute_individual_node(substitute);
        add_saturation_concept_reference(&mut process_context, original, reference, false);
        add_saturation_label_descriptor(
            &mut process_context,
            sat_label_set,
            &concepts,
            concept,
            false,
            INVALID,
        );
        let mut trigger_hash = std::collections::HashMap::new();

        assert!(analyser.merge_successor_saturation_label_triggers(
            &[original],
            &concepts,
            &process_context,
            &mut trigger_hash,
        ));
        assert_eq!(
            trigger_hash
                .get(&concepts.get(concept).get_concept_tag())
                .expect("substitute trigger")
                .indi_sat_node,
            substitute
        );
    }

    #[test]
    fn classification_message_analyser_multiple_successor_label_trigger_merge_records_substitute_reference(
    ) {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let mut concepts = Arena::new();
        let reference = concepts.push(concept_with_tag(CCATOM, 37, true));
        let label = concepts.push(concept_with_tag(CCATOM, 41, true));
        let original = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(11));
        let (substitute, sat_label_set) = add_saturation_label_set_node(&mut process_context);
        process_context
            .sat_node_mut(original)
            .set_substitute_individual_node(substitute);
        add_saturation_concept_reference(&mut process_context, original, reference, true);
        add_saturation_label_descriptor(
            &mut process_context,
            sat_label_set,
            &concepts,
            label,
            false,
            INVALID,
        );
        let mut trigger_hash = std::collections::HashMap::new();

        assert!(analyser.merge_successor_saturation_label_triggers(
            &[original],
            &concepts,
            &process_context,
            &mut trigger_hash,
        ));
        let reference_trigger = trigger_hash
            .get(&concepts.get(reference).get_concept_tag())
            .expect("substitute reference trigger");
        assert_eq!(reference_trigger.concept, reference);
        assert!(reference_trigger.negation_flag);
        assert_eq!(reference_trigger.indi_sat_node, original);

        let label_trigger = trigger_hash
            .get(&concepts.get(label).get_concept_tag())
            .expect("substitute label trigger");
        assert_eq!(label_trigger.concept, label);
        assert!(!label_trigger.negation_flag);
        assert_eq!(label_trigger.indi_sat_node, substitute);
    }

    #[test]
    fn classification_message_analyser_multiple_successor_label_trigger_merge_rejects_substitute_reference_trigger_conflict(
    ) {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let mut concepts = Arena::new();
        let reference = concepts.push(concept_with_tag(CCATOM, 37, true));
        let original = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(11));
        let substitute = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(13));
        process_context
            .sat_node_mut(original)
            .set_substitute_individual_node(substitute);
        add_saturation_concept_reference(&mut process_context, original, reference, false);
        let mut trigger_hash = std::collections::HashMap::new();
        trigger_hash.insert(
            concepts.get(reference).get_concept_tag(),
            ConceptNegationTriggerItem {
                trigger_flag: true,
                ..Default::default()
            },
        );

        assert!(!analyser.merge_successor_saturation_label_triggers(
            &[original],
            &concepts,
            &process_context,
            &mut trigger_hash,
        ));
    }

    #[test]
    fn classification_message_analyser_multiple_successor_label_trigger_merge_rejects_substitute_reference_polarity_conflict(
    ) {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let mut concepts = Arena::new();
        let reference = concepts.push(concept_with_tag(CCATOM, 37, true));
        let original = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(11));
        let substitute = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(13));
        process_context
            .sat_node_mut(original)
            .set_substitute_individual_node(substitute);
        add_saturation_concept_reference(&mut process_context, original, reference, false);
        let mut trigger_hash = std::collections::HashMap::new();
        trigger_hash.insert(
            concepts.get(reference).get_concept_tag(),
            ConceptNegationTriggerItem {
                concept: reference,
                negation_flag: true,
                ..Default::default()
            },
        );

        assert!(!analyser.merge_successor_saturation_label_triggers(
            &[original],
            &concepts,
            &process_context,
            &mut trigger_hash,
        ));
    }

    #[test]
    fn classification_message_analyser_multiple_successor_label_trigger_merge_records_multihop_substitute_references(
    ) {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let mut concepts = Arena::new();
        let first = concepts.push(concept_with_tag(CCATOM, 37, true));
        let second = concepts.push(concept_with_tag(CCATOM, 41, true));
        let original = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(11));
        let middle = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(13));
        let final_node = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(17));
        process_context
            .sat_node_mut(original)
            .set_substitute_individual_node(middle);
        process_context
            .sat_node_mut(middle)
            .set_substitute_individual_node(final_node);
        add_saturation_concept_reference(&mut process_context, original, first, false);
        add_saturation_concept_reference(&mut process_context, middle, second, true);
        let mut trigger_hash = std::collections::HashMap::new();

        assert!(analyser.merge_successor_saturation_label_triggers(
            &[original],
            &concepts,
            &process_context,
            &mut trigger_hash,
        ));
        assert_eq!(
            trigger_hash
                .get(&concepts.get(first).get_concept_tag())
                .expect("first substitute reference")
                .indi_sat_node,
            original
        );
        assert_eq!(
            trigger_hash
                .get(&concepts.get(second).get_concept_tag())
                .expect("second substitute reference")
                .indi_sat_node,
            middle
        );
    }

    #[test]
    fn classification_message_analyser_multiple_successor_recursive_jobs_prepend_existential_successor(
    ) {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let source = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(11));
        let ext_sat = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(13));
        let operand_sat = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(17));
        process_context
            .sat_node_mut(operand_sat)
            .set_completed(true);
        let mut concepts = Arena::new();
        let mut roles = Arena::new();
        let mut concept_process_datas = Arena::<ConceptProcessData>::new();
        let mut concept_reference_linking_datas =
            Arena::<ConceptSaturationReferenceLinkingData>::new();
        let mut saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let role = roles.push(role_with_tag(7, false));
        roles.get_mut(role).add_indirect_super_role_linker(NegLink {
            target: role,
            negated: false,
        });
        let operand = concepts.push(concept_with_tag(CCATOM, 31, true));
        let operand_ref = add_saturation_reference(&mut saturation_reference_linkings, operand_sat);
        let mut operand_ref_data = ConceptSaturationReferenceLinkingData::new();
        operand_ref_data.set_saturation_reference_linking_data(operand_ref, false);
        attach_concept_reference_data(
            &mut concepts,
            operand,
            &mut concept_process_datas,
            &mut concept_reference_linking_datas,
            operand_ref_data,
        );
        let mut some = concept_with_tag(CCSOME, 41, true);
        some.set_role(role);
        let some = concepts.push(some);
        let ext_ref = add_saturation_reference(&mut saturation_reference_linkings, ext_sat);
        let mut ext_ref_data = ConceptSaturationReferenceLinkingData::new();
        ext_ref_data.set_existential_successor_concept_saturation_reference_linking_data(ext_ref);
        attach_concept_reference_data(
            &mut concepts,
            some,
            &mut concept_process_datas,
            &mut concept_reference_linking_datas,
            ext_ref_data,
        );
        let mut trigger_hash = std::collections::HashMap::new();
        trigger_hash.insert(
            concepts.get(some).get_concept_tag(),
            ConceptNegationTriggerItem {
                concept: some,
                indi_sat_node: source,
                ..Default::default()
            },
        );
        let mut jobs = Vec::new();

        assert!(
            analyser.collect_multiple_successor_recursive_merge_jobs_from_triggers(
                &trigger_hash,
                &[],
                &[],
                &std::collections::HashSet::new(),
                &[(role, (operand, false))],
                &concepts,
                &roles,
                &concept_process_datas,
                &concept_reference_linking_datas,
                &saturation_reference_linkings,
                &process_context,
                None,
                &mut jobs,
            )
        );
        assert_eq!(jobs.len(), 1);
        assert_eq!(jobs[0].existential_sat_node, ext_sat);
        assert_eq!(jobs[0].successor_list, vec![ext_sat, operand_sat]);
        assert!(jobs[0].trivial_successor_propagated_concept_list.is_empty());
        assert!(jobs[0].backward_role_set.is_empty());
    }

    #[test]
    fn classification_message_analyser_multiple_successor_recursive_jobs_preserve_original_trivial_condition(
    ) {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let source = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(11));
        let ext_sat = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(13));
        let mut concepts = Arena::new();
        let mut roles = Arena::new();
        let mut concept_process_datas = Arena::<ConceptProcessData>::new();
        let mut concept_reference_linking_datas =
            Arena::<ConceptSaturationReferenceLinkingData>::new();
        let mut saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let role = roles.push(role_with_tag(7, false));
        let trivial = concepts.push(concept_with_tag(CCSUB, 31, true));
        let mut some = concept_with_tag(CCSOME, 41, true);
        some.set_role(role);
        let some = concepts.push(some);
        let ext_ref = add_saturation_reference(&mut saturation_reference_linkings, ext_sat);
        let mut ext_ref_data = ConceptSaturationReferenceLinkingData::new();
        ext_ref_data.set_existential_successor_concept_saturation_reference_linking_data(ext_ref);
        attach_concept_reference_data(
            &mut concepts,
            some,
            &mut concept_process_datas,
            &mut concept_reference_linking_datas,
            ext_ref_data,
        );
        let mut trigger_hash = std::collections::HashMap::new();
        trigger_hash.insert(
            concepts.get(some).get_concept_tag(),
            ConceptNegationTriggerItem {
                concept: some,
                indi_sat_node: source,
                ..Default::default()
            },
        );

        let mut empty_original_jobs = Vec::new();
        assert!(
            analyser.collect_multiple_successor_recursive_merge_jobs_from_triggers(
                &trigger_hash,
                &[],
                &[],
                &std::collections::HashSet::new(),
                &[],
                &concepts,
                &roles,
                &concept_process_datas,
                &concept_reference_linking_datas,
                &saturation_reference_linkings,
                &process_context,
                None,
                &mut empty_original_jobs,
            )
        );
        assert!(empty_original_jobs.is_empty());

        let mut jobs = Vec::new();
        assert!(
            analyser.collect_multiple_successor_recursive_merge_jobs_from_triggers(
                &trigger_hash,
                &[],
                &[(trivial, true)],
                &std::collections::HashSet::new(),
                &[],
                &concepts,
                &roles,
                &concept_process_datas,
                &concept_reference_linking_datas,
                &saturation_reference_linkings,
                &process_context,
                None,
                &mut jobs,
            )
        );
        assert_eq!(jobs.len(), 1);
        assert_eq!(jobs[0].successor_list, vec![ext_sat]);
        assert!(jobs[0].trivial_successor_propagated_concept_list.is_empty());
    }

    #[test]
    fn classification_message_analyser_multiple_successor_recursive_jobs_reject_missing_existential_saturation(
    ) {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let source = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(11));
        let operand_sat = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(17));
        process_context
            .sat_node_mut(operand_sat)
            .set_completed(true);
        let mut concepts = Arena::new();
        let mut roles = Arena::new();
        let mut concept_process_datas = Arena::<ConceptProcessData>::new();
        let mut concept_reference_linking_datas =
            Arena::<ConceptSaturationReferenceLinkingData>::new();
        let mut saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let role = roles.push(role_with_tag(7, false));
        roles.get_mut(role).add_indirect_super_role_linker(NegLink {
            target: role,
            negated: false,
        });
        let operand = concepts.push(concept_with_tag(CCATOM, 31, true));
        let operand_ref = add_saturation_reference(&mut saturation_reference_linkings, operand_sat);
        let mut operand_ref_data = ConceptSaturationReferenceLinkingData::new();
        operand_ref_data.set_saturation_reference_linking_data(operand_ref, false);
        attach_concept_reference_data(
            &mut concepts,
            operand,
            &mut concept_process_datas,
            &mut concept_reference_linking_datas,
            operand_ref_data,
        );
        let mut some = concept_with_tag(CCSOME, 41, true);
        some.set_role(role);
        let some = concepts.push(some);
        let mut trigger_hash = std::collections::HashMap::new();
        trigger_hash.insert(
            concepts.get(some).get_concept_tag(),
            ConceptNegationTriggerItem {
                concept: some,
                indi_sat_node: source,
                ..Default::default()
            },
        );
        let mut jobs = Vec::new();

        assert!(
            !analyser.collect_multiple_successor_recursive_merge_jobs_from_triggers(
                &trigger_hash,
                &[],
                &[],
                &std::collections::HashSet::new(),
                &[(role, (operand, false))],
                &concepts,
                &roles,
                &concept_process_datas,
                &concept_reference_linking_datas,
                &saturation_reference_linkings,
                &process_context,
                None,
                &mut jobs,
            )
        );
        assert!(jobs.is_empty());
    }

    #[test]
    fn classification_message_analyser_saturated_successor_dispatch_selects_single_and_decrements_limits(
    ) {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let existential = SatNodeId::new(7);
        let successor = SatNodeId::new(11);
        let trivial = ConceptId::new(13);
        let mut backward_roles = std::collections::HashSet::new();
        backward_roles.insert(RoleId::new(17));
        let mut remaining_count = 100;

        let dispatch = analyser
            .prepare_saturated_successor_model_merge_dispatch(
                existential,
                &[successor],
                &[(trivial, true)],
                &backward_roles,
                5,
                &mut remaining_count,
            )
            .expect("dispatch payload");

        assert_eq!(remaining_count, 99);
        assert_eq!(dispatch.kind, SaturatedSuccessorMergeDispatchKind::Single);
        assert_eq!(dispatch.existential_sat_node, existential);
        assert_eq!(dispatch.remaining_merging_depth, 4);
        assert_eq!(dispatch.successor_list, vec![successor]);
        assert_eq!(
            dispatch.trivial_successor_propagated_concept_list,
            vec![(trivial, true)]
        );
        assert_eq!(dispatch.backward_role_set, backward_roles);
    }

    #[test]
    fn classification_message_analyser_saturated_successor_dispatch_selects_multiple_for_non_single_count(
    ) {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let existential = SatNodeId::new(7);
        let successor_a = SatNodeId::new(11);
        let successor_b = SatNodeId::new(13);
        let mut remaining_count = 3;

        let dispatch = analyser
            .prepare_saturated_successor_model_merge_dispatch(
                existential,
                &[successor_a, successor_b],
                &[],
                &std::collections::HashSet::new(),
                2,
                &mut remaining_count,
            )
            .expect("multiple dispatch payload");

        assert_eq!(remaining_count, 2);
        assert_eq!(dispatch.kind, SaturatedSuccessorMergeDispatchKind::Multiple);
        assert_eq!(dispatch.remaining_merging_depth, 1);
        assert_eq!(dispatch.successor_list, vec![successor_a, successor_b]);
    }

    #[test]
    fn classification_message_analyser_saturated_successor_dispatch_preserves_predecrement_failure_order(
    ) {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut count = 5;
        assert!(analyser
            .prepare_saturated_successor_model_merge_dispatch(
                SatNodeId::new(7),
                &[SatNodeId::new(11)],
                &[],
                &std::collections::HashSet::new(),
                0,
                &mut count,
            )
            .is_none());
        assert_eq!(count, 5);

        let mut count = 0;
        assert!(analyser
            .prepare_saturated_successor_model_merge_dispatch(
                SatNodeId::new(7),
                &[SatNodeId::new(11)],
                &[],
                &std::collections::HashSet::new(),
                1,
                &mut count,
            )
            .is_none());
        assert_eq!(count, -1);
    }

    #[test]
    fn classification_message_analyser_saturated_successor_executor_preserves_predecrement_failure_order(
    ) {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let concepts = Arena::<Concept>::new();
        let roles = Arena::<Role>::new();
        let concept_process_datas = Arena::<ConceptProcessData>::new();
        let concept_reference_linking_datas = Arena::<ConceptSaturationReferenceLinkingData>::new();
        let saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let process_context = ProcessContext::new();
        let mut count = 5;

        assert!(!analyser.test_saturated_successor_model_mergable(
            SatNodeId::new(7),
            &[SatNodeId::new(11)],
            &[],
            &std::collections::HashSet::new(),
            0,
            &mut count,
            &concepts,
            &roles,
            &concept_process_datas,
            &concept_reference_linking_datas,
            &saturation_reference_linkings,
            &process_context,
            None,
        ));
        assert_eq!(count, 5);

        let mut count = 0;
        assert!(!analyser.test_saturated_successor_model_mergable(
            SatNodeId::new(7),
            &[SatNodeId::new(11)],
            &[],
            &std::collections::HashSet::new(),
            1,
            &mut count,
            &concepts,
            &roles,
            &concept_process_datas,
            &concept_reference_linking_datas,
            &saturation_reference_linkings,
            &process_context,
            None,
        ));
        assert_eq!(count, -1);
    }

    #[test]
    fn classification_message_analyser_saturated_successor_job_dispatches_share_count_budget() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut first_backward = std::collections::HashSet::new();
        first_backward.insert(RoleId::new(31));
        let jobs = vec![
            SaturatedSuccessorMergeJob {
                existential_sat_node: SatNodeId::new(7),
                successor_list: vec![SatNodeId::new(11)],
                trivial_successor_propagated_concept_list: vec![(ConceptId::new(13), true)],
                backward_role_set: first_backward.clone(),
            },
            SaturatedSuccessorMergeJob {
                existential_sat_node: SatNodeId::new(17),
                successor_list: vec![SatNodeId::new(19), SatNodeId::new(23)],
                trivial_successor_propagated_concept_list: Vec::new(),
                backward_role_set: std::collections::HashSet::new(),
            },
        ];
        let mut count = 2;
        let mut dispatches = Vec::new();

        assert!(analyser.prepare_saturated_successor_merge_job_dispatches(
            &jobs,
            4,
            &mut count,
            &mut dispatches,
        ));
        assert_eq!(count, 0);
        assert_eq!(dispatches.len(), 2);
        assert_eq!(
            dispatches[0].kind,
            SaturatedSuccessorMergeDispatchKind::Single
        );
        assert_eq!(dispatches[0].remaining_merging_depth, 3);
        assert_eq!(dispatches[0].backward_role_set, first_backward);
        assert_eq!(
            dispatches[1].kind,
            SaturatedSuccessorMergeDispatchKind::Multiple
        );
        assert_eq!(
            dispatches[1].successor_list,
            vec![SatNodeId::new(19), SatNodeId::new(23)]
        );

        let mut count = 1;
        let mut dispatches = Vec::new();
        assert!(!analyser.prepare_saturated_successor_merge_job_dispatches(
            &jobs,
            4,
            &mut count,
            &mut dispatches,
        ));
        assert_eq!(count, -1);
        assert_eq!(dispatches.len(), 1);
    }

    #[test]
    fn classification_message_analyser_executes_terminal_single_successor_dispatch() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let concepts = Arena::<Concept>::new();
        let roles = Arena::<Role>::new();
        let concept_process_datas = Arena::<ConceptProcessData>::new();
        let concept_reference_linking_datas = Arena::<ConceptSaturationReferenceLinkingData>::new();
        let saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let (existential, _) = add_saturation_label_set_node(&mut process_context);
        let job = SaturatedSuccessorMergeJob {
            existential_sat_node: existential,
            successor_list: vec![existential],
            trivial_successor_propagated_concept_list: Vec::new(),
            backward_role_set: std::collections::HashSet::new(),
        };
        let mut remaining_count = 3;

        assert!(analyser.execute_saturated_successor_merge_job(
            &job,
            2,
            &mut remaining_count,
            &concepts,
            &roles,
            &concept_process_datas,
            &concept_reference_linking_datas,
            &saturation_reference_linkings,
            &process_context,
            None,
        ));
        assert_eq!(remaining_count, 2);
    }

    #[test]
    fn classification_message_analyser_execution_preserves_depth_gate_before_child_count_decrement()
    {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let mut concepts = Arena::new();
        let mut roles = Arena::new();
        let mut concept_process_datas = Arena::<ConceptProcessData>::new();
        let mut concept_reference_linking_datas =
            Arena::<ConceptSaturationReferenceLinkingData>::new();
        let mut saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let (existential, sat_label_set) = add_saturation_label_set_node(&mut process_context);
        let ext_sat = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(13));
        let role = roles.push(role_with_tag(7, false));
        let trivial = concepts.push(concept_with_tag(CCSUB, 31, true));
        let mut some = concept_with_tag(CCSOME, 41, true);
        some.set_role(role);
        let some = concepts.push(some);
        let ext_ref = add_saturation_reference(&mut saturation_reference_linkings, ext_sat);
        let mut ext_ref_data = ConceptSaturationReferenceLinkingData::new();
        ext_ref_data.set_existential_successor_concept_saturation_reference_linking_data(ext_ref);
        attach_concept_reference_data(
            &mut concepts,
            some,
            &mut concept_process_datas,
            &mut concept_reference_linking_datas,
            ext_ref_data,
        );
        let con_sat_des = add_saturation_label_descriptor(
            &mut process_context,
            sat_label_set,
            &concepts,
            some,
            false,
            INVALID,
        );
        set_saturation_label_descriptor_linker(&mut process_context, sat_label_set, &[con_sat_des]);
        let job = SaturatedSuccessorMergeJob {
            existential_sat_node: existential,
            successor_list: vec![existential],
            trivial_successor_propagated_concept_list: vec![(trivial, true)],
            backward_role_set: std::collections::HashSet::new(),
        };
        let mut remaining_count = 5;

        assert!(!analyser.execute_saturated_successor_merge_job(
            &job,
            1,
            &mut remaining_count,
            &concepts,
            &roles,
            &concept_process_datas,
            &concept_reference_linking_datas,
            &saturation_reference_linkings,
            &process_context,
            None,
        ));
        assert_eq!(remaining_count, 4);
    }

    #[test]
    fn classification_message_analyser_single_successor_prep_accepts_matching_negated_sub_descriptor(
    ) {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let mut concepts = Arena::new();
        let sub = concepts.push(concept_with_tag(CCSUB, 31, true));
        let (existential, sat_label_set) = add_saturation_label_set_node(&mut process_context);
        add_saturation_label_descriptor(
            &mut process_context,
            sat_label_set,
            &concepts,
            sub,
            true,
            INVALID,
        );

        let state = analyser
            .prepare_single_saturated_successor_merge_state(
                existential,
                &[(sub, true)],
                &std::collections::HashSet::new(),
                &concepts,
                &process_context,
            )
            .expect("single successor prep");

        assert_eq!(state.sub_resolved_existential_sat_node, existential);
        assert_eq!(state.saturation_label_set, sat_label_set);
        assert!(state.successor_influence_concepts.is_empty());
    }

    #[test]
    fn classification_message_analyser_single_successor_prep_rejects_sub_descriptor_conflicts() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let mut concepts = Arena::new();
        let sub = concepts.push(concept_with_tag(CCSUB, 31, true));
        let (existential, sat_label_set) = add_saturation_label_set_node(&mut process_context);
        add_saturation_label_descriptor(
            &mut process_context,
            sat_label_set,
            &concepts,
            sub,
            false,
            INVALID,
        );

        assert!(analyser
            .prepare_single_saturated_successor_merge_state(
                existential,
                &[(sub, true)],
                &std::collections::HashSet::new(),
                &concepts,
                &process_context,
            )
            .is_none());

        process_context
            .reapply_con_sat_label_set_mut(sat_label_set)
            .concept_des_dep_hash
            .insert(
                concepts.get(sub).get_concept_tag(),
                ConceptSaturationDescriptorReapplyData {
                    con_sat_des: super::super::super::saturation::satellites::ConceptSaturationDescriptorId::NONE,
                    imp_reapply_con_sat_des: super::super::super::saturation::satellites::ImplicationReapplyConceptSaturationDescriptorId::new(77),
                },
            );
        assert!(analyser
            .prepare_single_saturated_successor_merge_state(
                existential,
                &[(sub, true)],
                &std::collections::HashSet::new(),
                &concepts,
                &process_context,
            )
            .is_none());
    }

    #[test]
    fn classification_message_analyser_single_successor_prep_checks_substitute_reference_fallback()
    {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let mut concepts = Arena::new();
        let sub = concepts.push(concept_with_tag(CCSUB, 31, true));
        let original = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(11));
        let (substitute, _) = add_saturation_label_set_node(&mut process_context);
        process_context
            .sat_node_mut(original)
            .set_substitute_individual_node(substitute);
        add_saturation_concept_reference(&mut process_context, original, sub, false);

        assert!(analyser
            .prepare_single_saturated_successor_merge_state(
                original,
                &[(sub, true)],
                &std::collections::HashSet::new(),
                &concepts,
                &process_context,
            )
            .is_none());

        add_saturation_concept_reference(&mut process_context, original, sub, true);
        let state = analyser
            .prepare_single_saturated_successor_merge_state(
                original,
                &[(sub, true)],
                &std::collections::HashSet::new(),
                &concepts,
                &process_context,
            )
            .expect("matching substitute reference");
        assert_eq!(state.sub_resolved_existential_sat_node, substitute);
    }

    #[test]
    fn classification_message_analyser_single_successor_prep_collects_all_influence_and_rejects_backward_role(
    ) {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let mut concepts = Arena::new();
        let role = RoleId::new(7);
        let operand = concepts.push(concept_with_tag(CCATOM, 31, true));
        let mut all = concept_with_tag(CCALL, 41, true);
        all.set_role(role);
        all.add_operand_linker(operand, true);
        let all = concepts.push(all);
        let (existential, _) = add_saturation_label_set_node(&mut process_context);

        let state = analyser
            .prepare_single_saturated_successor_merge_state(
                existential,
                &[(all, false)],
                &std::collections::HashSet::new(),
                &concepts,
                &process_context,
            )
            .expect("ALL influence prep");
        assert_eq!(
            state.successor_influence_concepts,
            vec![(role, (operand, true))]
        );

        let mut backward_roles = std::collections::HashSet::new();
        backward_roles.insert(role);
        assert!(analyser
            .prepare_single_saturated_successor_merge_state(
                existential,
                &[(all, false)],
                &backward_roles,
                &concepts,
                &process_context,
            )
            .is_none());
    }

    #[test]
    fn classification_message_analyser_single_successor_non_extension_jobs_prepend_existential_successor(
    ) {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let mut concepts = Arena::new();
        let mut roles = Arena::new();
        let mut concept_process_datas = Arena::<ConceptProcessData>::new();
        let mut concept_reference_linking_datas =
            Arena::<ConceptSaturationReferenceLinkingData>::new();
        let mut saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let (existential, sat_label_set) = add_saturation_label_set_node(&mut process_context);
        let ext_sat = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(13));
        let operand_sat = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(17));
        process_context
            .sat_node_mut(operand_sat)
            .set_completed(true);
        let role = roles.push(role_with_tag(7, false));
        roles.get_mut(role).add_indirect_super_role_linker(NegLink {
            target: role,
            negated: false,
        });
        let operand = concepts.push(concept_with_tag(CCATOM, 31, true));
        let operand_ref = add_saturation_reference(&mut saturation_reference_linkings, operand_sat);
        let mut operand_ref_data = ConceptSaturationReferenceLinkingData::new();
        operand_ref_data.set_saturation_reference_linking_data(operand_ref, false);
        attach_concept_reference_data(
            &mut concepts,
            operand,
            &mut concept_process_datas,
            &mut concept_reference_linking_datas,
            operand_ref_data,
        );
        let mut some = concept_with_tag(CCSOME, 41, true);
        some.set_role(role);
        let some = concepts.push(some);
        let ext_ref = add_saturation_reference(&mut saturation_reference_linkings, ext_sat);
        let mut ext_ref_data = ConceptSaturationReferenceLinkingData::new();
        ext_ref_data.set_existential_successor_concept_saturation_reference_linking_data(ext_ref);
        attach_concept_reference_data(
            &mut concepts,
            some,
            &mut concept_process_datas,
            &mut concept_reference_linking_datas,
            ext_ref_data,
        );
        let con_sat_des = add_saturation_label_descriptor(
            &mut process_context,
            sat_label_set,
            &concepts,
            some,
            false,
            INVALID,
        );
        set_saturation_label_descriptor_linker(&mut process_context, sat_label_set, &[con_sat_des]);
        let state = SingleSaturatedSuccessorMergeState {
            sub_resolved_existential_sat_node: existential,
            saturation_label_set: sat_label_set,
            successor_influence_concepts: vec![(role, (operand, false))],
        };
        let mut jobs = Vec::new();

        assert!(
            analyser.collect_single_successor_non_extension_recursive_merge_jobs(
                existential,
                &[],
                &[],
                &state,
                &concepts,
                &roles,
                &concept_process_datas,
                &concept_reference_linking_datas,
                &saturation_reference_linkings,
                &process_context,
                None,
                &mut jobs,
            )
        );
        assert_eq!(jobs.len(), 1);
        assert_eq!(jobs[0].existential_sat_node, ext_sat);
        assert_eq!(jobs[0].successor_list, vec![ext_sat, operand_sat]);
        assert!(jobs[0].trivial_successor_propagated_concept_list.is_empty());
        assert!(jobs[0].backward_role_set.is_empty());
    }

    #[test]
    fn classification_message_analyser_single_successor_non_extension_jobs_preserve_original_trivial_gate(
    ) {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let mut concepts = Arena::new();
        let mut roles = Arena::new();
        let mut concept_process_datas = Arena::<ConceptProcessData>::new();
        let mut concept_reference_linking_datas =
            Arena::<ConceptSaturationReferenceLinkingData>::new();
        let mut saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let (existential, sat_label_set) = add_saturation_label_set_node(&mut process_context);
        let ext_sat = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(13));
        let role = roles.push(role_with_tag(7, false));
        let trivial = concepts.push(concept_with_tag(CCSUB, 31, true));
        let mut some = concept_with_tag(CCSOME, 41, true);
        some.set_role(role);
        let some = concepts.push(some);
        let ext_ref = add_saturation_reference(&mut saturation_reference_linkings, ext_sat);
        let mut ext_ref_data = ConceptSaturationReferenceLinkingData::new();
        ext_ref_data.set_existential_successor_concept_saturation_reference_linking_data(ext_ref);
        attach_concept_reference_data(
            &mut concepts,
            some,
            &mut concept_process_datas,
            &mut concept_reference_linking_datas,
            ext_ref_data,
        );
        let con_sat_des = add_saturation_label_descriptor(
            &mut process_context,
            sat_label_set,
            &concepts,
            some,
            false,
            INVALID,
        );
        set_saturation_label_descriptor_linker(&mut process_context, sat_label_set, &[con_sat_des]);
        let state = SingleSaturatedSuccessorMergeState {
            sub_resolved_existential_sat_node: existential,
            saturation_label_set: sat_label_set,
            successor_influence_concepts: Vec::new(),
        };

        let mut jobs = Vec::new();
        assert!(
            analyser.collect_single_successor_non_extension_recursive_merge_jobs(
                existential,
                &[],
                &[],
                &state,
                &concepts,
                &roles,
                &concept_process_datas,
                &concept_reference_linking_datas,
                &saturation_reference_linkings,
                &process_context,
                None,
                &mut jobs,
            )
        );
        assert!(jobs.is_empty());

        assert!(
            analyser.collect_single_successor_non_extension_recursive_merge_jobs(
                existential,
                &[],
                &[(trivial, true)],
                &state,
                &concepts,
                &roles,
                &concept_process_datas,
                &concept_reference_linking_datas,
                &saturation_reference_linkings,
                &process_context,
                None,
                &mut jobs,
            )
        );
        assert_eq!(jobs.len(), 1);
        assert_eq!(jobs[0].successor_list, vec![ext_sat]);
    }

    #[test]
    fn classification_message_analyser_single_successor_non_extension_jobs_skip_successor_extension_branch(
    ) {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let mut concepts = Arena::new();
        let roles = Arena::<Role>::new();
        let concept_process_datas = Arena::<ConceptProcessData>::new();
        let concept_reference_linking_datas = Arena::<ConceptSaturationReferenceLinkingData>::new();
        let saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let (existential, sat_label_set) = add_saturation_label_set_node(&mut process_context);
        process_context
            .sat_node_mut(existential)
            .direct_status_flags
            .add_flags_code(IndividualSaturationProcessNodeStatusFlags::INDSUCCESSORNODEEXTENSIONS);
        let mut some = concept_with_tag(CCSOME, 41, true);
        some.set_role(RoleId::new(7));
        let some = concepts.push(some);
        let con_sat_des = add_saturation_label_descriptor(
            &mut process_context,
            sat_label_set,
            &concepts,
            some,
            false,
            INVALID,
        );
        set_saturation_label_descriptor_linker(&mut process_context, sat_label_set, &[con_sat_des]);
        let state = SingleSaturatedSuccessorMergeState {
            sub_resolved_existential_sat_node: existential,
            saturation_label_set: sat_label_set,
            successor_influence_concepts: Vec::new(),
        };
        let mut jobs = Vec::new();

        assert!(
            analyser.collect_single_successor_non_extension_recursive_merge_jobs(
                existential,
                &[],
                &[(ConceptId::new(31), true)],
                &state,
                &concepts,
                &roles,
                &concept_process_datas,
                &concept_reference_linking_datas,
                &saturation_reference_linkings,
                &process_context,
                None,
                &mut jobs,
            )
        );
        assert!(jobs.is_empty());
    }

    #[test]
    fn classification_message_analyser_linked_successor_extension_jobs_collect_active_matching_creation_role(
    ) {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let source = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(11));
        let ext_successor =
            process_context.alloc_sat_node(IndividualSaturationProcessNode::new(13));
        let operand_sat = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(17));
        process_context
            .sat_node_mut(operand_sat)
            .set_completed(true);
        let mut concepts = Arena::new();
        let mut roles = Arena::new();
        let mut concept_process_datas = Arena::<ConceptProcessData>::new();
        let mut concept_reference_linking_datas =
            Arena::<ConceptSaturationReferenceLinkingData>::new();
        let mut saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let role = roles.push(role_with_tag(7, false));
        roles.get_mut(role).add_indirect_super_role_linker(NegLink {
            target: role,
            negated: false,
        });
        let operand = concepts.push(concept_with_tag(CCATOM, 31, true));
        let operand_ref = add_saturation_reference(&mut saturation_reference_linkings, operand_sat);
        let mut operand_ref_data = ConceptSaturationReferenceLinkingData::new();
        operand_ref_data.set_saturation_reference_linking_data(operand_ref, false);
        attach_concept_reference_data(
            &mut concepts,
            operand,
            &mut concept_process_datas,
            &mut concept_reference_linking_datas,
            operand_ref_data,
        );
        add_linked_role_saturation_successor(
            &mut process_context,
            source,
            role,
            ext_successor,
            1,
            vec![NegLink {
                target: role,
                negated: false,
            }],
        );
        let mut jobs = Vec::new();

        assert!(
            analyser.collect_linked_successor_extension_recursive_merge_jobs(
                source,
                &[],
                &[],
                &[(role, (operand, false))],
                &concepts,
                &roles,
                &concept_process_datas,
                &concept_reference_linking_datas,
                &saturation_reference_linkings,
                &process_context,
                &mut jobs,
            )
        );
        assert_eq!(jobs.len(), 1);
        assert_eq!(jobs[0].existential_sat_node, ext_successor);
        assert_eq!(jobs[0].successor_list, vec![ext_successor, operand_sat]);
        assert!(jobs[0].trivial_successor_propagated_concept_list.is_empty());
    }

    #[test]
    fn classification_message_analyser_linked_successor_extension_jobs_ignore_inactive_negated_and_nonmatching_creation_roles(
    ) {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let source = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(11));
        let succ_a = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(13));
        let succ_b = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(17));
        let succ_c = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(19));
        let mut concepts = Arena::new();
        let mut roles = Arena::new();
        let concept_process_datas = Arena::<ConceptProcessData>::new();
        let concept_reference_linking_datas = Arena::<ConceptSaturationReferenceLinkingData>::new();
        let saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let role = roles.push(role_with_tag(7, false));
        roles.get_mut(role).add_indirect_super_role_linker(NegLink {
            target: role,
            negated: false,
        });
        let other_role = roles.push(role_with_tag(9, false));
        let trivial = concepts.push(concept_with_tag(CCSUB, 31, true));
        add_linked_role_saturation_successor(
            &mut process_context,
            source,
            role,
            succ_a,
            0,
            vec![NegLink {
                target: role,
                negated: false,
            }],
        );
        add_linked_role_saturation_successor(
            &mut process_context,
            source,
            role,
            succ_b,
            1,
            vec![NegLink {
                target: role,
                negated: true,
            }],
        );
        add_linked_role_saturation_successor(
            &mut process_context,
            source,
            role,
            succ_c,
            1,
            vec![NegLink {
                target: other_role,
                negated: false,
            }],
        );
        let mut jobs = Vec::new();

        assert!(
            analyser.collect_linked_successor_extension_recursive_merge_jobs(
                source,
                &[],
                &[(trivial, true)],
                &[],
                &concepts,
                &roles,
                &concept_process_datas,
                &concept_reference_linking_datas,
                &saturation_reference_linkings,
                &process_context,
                &mut jobs,
            )
        );
        assert!(jobs.is_empty());
    }

    #[test]
    fn classification_message_analyser_linked_successor_extension_jobs_reject_invalid_ext_successor_node(
    ) {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let source = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(11));
        let mut concepts = Arena::new();
        let mut roles = Arena::new();
        let concept_process_datas = Arena::<ConceptProcessData>::new();
        let concept_reference_linking_datas = Arena::<ConceptSaturationReferenceLinkingData>::new();
        let saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let role = roles.push(role_with_tag(7, false));
        roles.get_mut(role).add_indirect_super_role_linker(NegLink {
            target: role,
            negated: false,
        });
        let trivial = concepts.push(concept_with_tag(CCSUB, 31, true));
        add_linked_role_saturation_successor(
            &mut process_context,
            source,
            role,
            SatNodeId::new(999),
            1,
            vec![NegLink {
                target: role,
                negated: false,
            }],
        );
        let mut jobs = Vec::new();

        assert!(
            !analyser.collect_linked_successor_extension_recursive_merge_jobs(
                source,
                &[],
                &[(trivial, true)],
                &[],
                &concepts,
                &roles,
                &concept_process_datas,
                &concept_reference_linking_datas,
                &saturation_reference_linkings,
                &process_context,
                &mut jobs,
            )
        );
        assert!(jobs.is_empty());
    }

    #[test]
    fn classification_message_analyser_single_successor_wrapper_dispatches_non_extension_jobs() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let mut concepts = Arena::new();
        let mut roles = Arena::new();
        let mut concept_process_datas = Arena::<ConceptProcessData>::new();
        let mut concept_reference_linking_datas =
            Arena::<ConceptSaturationReferenceLinkingData>::new();
        let mut saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let (existential, sat_label_set) = add_saturation_label_set_node(&mut process_context);
        let ext_sat = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(13));
        let role = roles.push(role_with_tag(7, false));
        let trivial = concepts.push(concept_with_tag(CCSUB, 31, true));
        let mut some = concept_with_tag(CCSOME, 41, true);
        some.set_role(role);
        let some = concepts.push(some);
        let ext_ref = add_saturation_reference(&mut saturation_reference_linkings, ext_sat);
        let mut ext_ref_data = ConceptSaturationReferenceLinkingData::new();
        ext_ref_data.set_existential_successor_concept_saturation_reference_linking_data(ext_ref);
        attach_concept_reference_data(
            &mut concepts,
            some,
            &mut concept_process_datas,
            &mut concept_reference_linking_datas,
            ext_ref_data,
        );
        let con_sat_des = add_saturation_label_descriptor(
            &mut process_context,
            sat_label_set,
            &concepts,
            some,
            false,
            INVALID,
        );
        set_saturation_label_descriptor_linker(&mut process_context, sat_label_set, &[con_sat_des]);
        let mut remaining_count = 3;
        let mut dispatches = Vec::new();

        assert!(
            analyser.prepare_single_saturated_successor_model_merge_dispatches(
                existential,
                &[existential],
                &[(trivial, true)],
                &std::collections::HashSet::new(),
                4,
                &mut remaining_count,
                &concepts,
                &roles,
                &concept_process_datas,
                &concept_reference_linking_datas,
                &saturation_reference_linkings,
                &process_context,
                None,
                &mut dispatches,
            )
        );

        assert_eq!(remaining_count, 2);
        assert_eq!(dispatches.len(), 1);
        assert_eq!(
            dispatches[0].kind,
            SaturatedSuccessorMergeDispatchKind::Single
        );
        assert_eq!(dispatches[0].existential_sat_node, ext_sat);
        assert_eq!(dispatches[0].successor_list, vec![ext_sat]);
        assert_eq!(dispatches[0].remaining_merging_depth, 3);
    }

    #[test]
    fn classification_message_analyser_multiple_successor_wrapper_dispatches_triggers_before_extensions(
    ) {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let mut concepts = Arena::new();
        let mut roles = Arena::new();
        let mut concept_process_datas = Arena::<ConceptProcessData>::new();
        let mut concept_reference_linking_datas =
            Arena::<ConceptSaturationReferenceLinkingData>::new();
        let mut saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let (trigger_source, trigger_label_set) =
            add_saturation_label_set_node(&mut process_context);
        let linked_source =
            process_context.alloc_sat_node(IndividualSaturationProcessNode::new(17));
        let trigger_ext = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(19));
        let linked_ext = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(23));
        let role = roles.push(role_with_tag(7, false));
        roles.get_mut(role).add_indirect_super_role_linker(NegLink {
            target: role,
            negated: false,
        });
        let trivial = concepts.push(concept_with_tag(CCSUB, 31, true));
        let mut some = concept_with_tag(CCSOME, 41, true);
        some.set_role(role);
        let some = concepts.push(some);
        let trigger_ext_ref =
            add_saturation_reference(&mut saturation_reference_linkings, trigger_ext);
        let mut trigger_ext_ref_data = ConceptSaturationReferenceLinkingData::new();
        trigger_ext_ref_data
            .set_existential_successor_concept_saturation_reference_linking_data(trigger_ext_ref);
        attach_concept_reference_data(
            &mut concepts,
            some,
            &mut concept_process_datas,
            &mut concept_reference_linking_datas,
            trigger_ext_ref_data,
        );
        let con_sat_des = add_saturation_label_descriptor(
            &mut process_context,
            trigger_label_set,
            &concepts,
            some,
            false,
            INVALID,
        );
        set_saturation_label_descriptor_linker(
            &mut process_context,
            trigger_label_set,
            &[con_sat_des],
        );
        add_linked_role_saturation_successor(
            &mut process_context,
            linked_source,
            role,
            linked_ext,
            1,
            vec![NegLink {
                target: role,
                negated: false,
            }],
        );
        let mut remaining_count = 4;
        let mut dispatches = Vec::new();

        assert!(
            analyser.prepare_multiple_saturated_successor_model_merge_dispatches(
                trigger_source,
                &[trigger_source, linked_source],
                &[(trivial, true)],
                &std::collections::HashSet::new(),
                5,
                &mut remaining_count,
                &concepts,
                &roles,
                &concept_process_datas,
                &concept_reference_linking_datas,
                &saturation_reference_linkings,
                &process_context,
                None,
                &mut dispatches,
            )
        );

        assert_eq!(remaining_count, 2);
        assert_eq!(dispatches.len(), 2);
        assert_eq!(dispatches[0].existential_sat_node, trigger_ext);
        assert_eq!(dispatches[1].existential_sat_node, linked_ext);
        assert_eq!(dispatches[0].successor_list, vec![trigger_ext]);
        assert_eq!(dispatches[1].successor_list, vec![linked_ext]);
    }

    #[test]
    fn classification_message_analyser_saturated_existentials_wrapper_dispatches_non_extension_descriptor(
    ) {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let (node, _) = add_completion_label_set_node(&mut process_context);
        let (saturation_node, sat_label_set) = add_saturation_label_set_node(&mut process_context);
        let ext_sat = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(13));
        let mut concepts = Arena::new();
        let mut roles = Arena::new();
        let mut concept_process_datas = Arena::<ConceptProcessData>::new();
        let mut concept_reference_linking_datas =
            Arena::<ConceptSaturationReferenceLinkingData>::new();
        let mut saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let role = roles.push(role_with_tag(7, false));
        roles.get_mut(role).add_indirect_super_role_linker(NegLink {
            target: role,
            negated: false,
        });
        let sub = concepts.push(concept_with_tag(CCSUB, 31, true));
        let mut reapply_some = concept_with_tag(CCSOME, 33, true);
        reapply_some.add_operand_linker(sub, false);
        let reapply_some = concepts.push(reapply_some);
        let mut reapply_con_des = ConceptDescriptor::new();
        reapply_con_des.concept = reapply_some;
        reapply_con_des.negated = true;
        let reapply_con_des = process_context.alloc_con_desc(reapply_con_des);
        let reapply = process_context.alloc_reapply_con_desc(ReapplyConceptDescriptor::new(
            reapply_con_des,
            TrackPointId::NONE,
            false,
        ));
        process_context.node_add_role_reapply_concept_descriptor(node, role, reapply);
        let mut some = concept_with_tag(CCSOME, 41, true);
        some.set_role(role);
        let some = concepts.push(some);
        let ext_ref = add_saturation_reference(&mut saturation_reference_linkings, ext_sat);
        let mut ext_ref_data = ConceptSaturationReferenceLinkingData::new();
        ext_ref_data.set_existential_successor_concept_saturation_reference_linking_data(ext_ref);
        attach_concept_reference_data(
            &mut concepts,
            some,
            &mut concept_process_datas,
            &mut concept_reference_linking_datas,
            ext_ref_data,
        );
        let con_sat_des = add_saturation_label_descriptor(
            &mut process_context,
            sat_label_set,
            &concepts,
            some,
            false,
            INVALID,
        );
        set_saturation_label_descriptor_linker(&mut process_context, sat_label_set, &[con_sat_des]);
        let mut dispatches = Vec::new();

        assert!(
            analyser.prepare_saturated_existentials_model_merge_dispatches(
                node,
                saturation_node,
                &concepts,
                &roles,
                &concept_process_datas,
                &concept_reference_linking_datas,
                &saturation_reference_linkings,
                &mut process_context,
                None,
                &mut dispatches,
            )
        );

        assert_eq!(dispatches.len(), 1);
        assert_eq!(
            dispatches[0].kind,
            SaturatedSuccessorMergeDispatchKind::Single
        );
        assert_eq!(dispatches[0].existential_sat_node, ext_sat);
        assert_eq!(dispatches[0].successor_list, vec![ext_sat]);
        assert_eq!(
            dispatches[0].trivial_successor_propagated_concept_list,
            vec![(sub, true)]
        );
        assert_eq!(dispatches[0].remaining_merging_depth, 4);
    }

    #[test]
    fn classification_message_analyser_saturated_existentials_wrapper_dispatches_linked_extension_successor(
    ) {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let (node, _) = add_completion_label_set_node(&mut process_context);
        let saturation_node =
            process_context.alloc_sat_node(IndividualSaturationProcessNode::new(11));
        let ext_sat = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(13));
        let mut concepts = Arena::new();
        let mut roles = Arena::new();
        let concept_process_datas = Arena::<ConceptProcessData>::new();
        let concept_reference_linking_datas = Arena::<ConceptSaturationReferenceLinkingData>::new();
        let saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let role = roles.push(role_with_tag(7, false));
        roles.get_mut(role).add_indirect_super_role_linker(NegLink {
            target: role,
            negated: false,
        });
        let sub = concepts.push(concept_with_tag(CCSUB, 31, true));
        let mut reapply_some = concept_with_tag(CCSOME, 33, true);
        reapply_some.add_operand_linker(sub, false);
        let reapply_some = concepts.push(reapply_some);
        let mut reapply_con_des = ConceptDescriptor::new();
        reapply_con_des.concept = reapply_some;
        reapply_con_des.negated = true;
        let reapply_con_des = process_context.alloc_con_desc(reapply_con_des);
        let reapply = process_context.alloc_reapply_con_desc(ReapplyConceptDescriptor::new(
            reapply_con_des,
            TrackPointId::NONE,
            false,
        ));
        process_context.node_add_role_reapply_concept_descriptor(node, role, reapply);
        add_linked_role_saturation_successor(
            &mut process_context,
            saturation_node,
            role,
            ext_sat,
            1,
            vec![NegLink {
                target: role,
                negated: false,
            }],
        );
        let mut dispatches = Vec::new();

        assert!(
            analyser.prepare_saturated_existentials_model_merge_dispatches(
                node,
                saturation_node,
                &concepts,
                &roles,
                &concept_process_datas,
                &concept_reference_linking_datas,
                &saturation_reference_linkings,
                &mut process_context,
                None,
                &mut dispatches,
            )
        );

        assert_eq!(dispatches.len(), 1);
        assert_eq!(dispatches[0].existential_sat_node, ext_sat);
        assert_eq!(dispatches[0].successor_list, vec![ext_sat]);
        assert_eq!(
            dispatches[0].trivial_successor_propagated_concept_list,
            vec![(sub, true)]
        );
        assert_eq!(dispatches[0].remaining_merging_depth, 4);
    }

    #[test]
    fn classification_message_analyser_saturated_existentials_live_executes_successor_merge() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let (node, _) = add_completion_label_set_node(&mut process_context);
        let (saturation_node, sat_label_set) = add_saturation_label_set_node(&mut process_context);
        let (ext_sat, ext_sat_label_set) = add_saturation_label_set_node(&mut process_context);
        let mut concepts = Arena::new();
        let mut roles = Arena::new();
        let mut concept_process_datas = Arena::<ConceptProcessData>::new();
        let mut concept_reference_linking_datas =
            Arena::<ConceptSaturationReferenceLinkingData>::new();
        let mut saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let role = roles.push(role_with_tag(7, false));
        roles.get_mut(role).add_indirect_super_role_linker(NegLink {
            target: role,
            negated: false,
        });
        let sub = concepts.push(concept_with_tag(CCSUB, 31, true));
        add_saturation_label_descriptor(
            &mut process_context,
            ext_sat_label_set,
            &concepts,
            sub,
            true,
            INVALID,
        );
        let mut reapply_some = concept_with_tag(CCSOME, 33, true);
        reapply_some.add_operand_linker(sub, false);
        let reapply_some = concepts.push(reapply_some);
        let mut reapply_con_des = ConceptDescriptor::new();
        reapply_con_des.concept = reapply_some;
        reapply_con_des.negated = true;
        let reapply_con_des = process_context.alloc_con_desc(reapply_con_des);
        let reapply = process_context.alloc_reapply_con_desc(ReapplyConceptDescriptor::new(
            reapply_con_des,
            TrackPointId::NONE,
            false,
        ));
        process_context.node_add_role_reapply_concept_descriptor(node, role, reapply);
        let mut some = concept_with_tag(CCSOME, 41, true);
        some.set_role(role);
        let some = concepts.push(some);
        let ext_ref = add_saturation_reference(&mut saturation_reference_linkings, ext_sat);
        let mut ext_ref_data = ConceptSaturationReferenceLinkingData::new();
        ext_ref_data.set_existential_successor_concept_saturation_reference_linking_data(ext_ref);
        attach_concept_reference_data(
            &mut concepts,
            some,
            &mut concept_process_datas,
            &mut concept_reference_linking_datas,
            ext_ref_data,
        );
        let con_sat_des = add_saturation_label_descriptor(
            &mut process_context,
            sat_label_set,
            &concepts,
            some,
            false,
            INVALID,
        );
        set_saturation_label_descriptor_linker(&mut process_context, sat_label_set, &[con_sat_des]);

        assert!(analyser.test_saturated_existentials_model_mergable(
            node,
            saturation_node,
            &concepts,
            &roles,
            &concept_process_datas,
            &concept_reference_linking_datas,
            &saturation_reference_linkings,
            &mut process_context,
            None,
        ));
    }

    #[test]
    fn classification_message_analyser_saturated_existentials_live_rejects_dispatchable_invalid_child(
    ) {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let (node, _) = add_completion_label_set_node(&mut process_context);
        let (saturation_node, sat_label_set) = add_saturation_label_set_node(&mut process_context);
        let ext_sat = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(13));
        let mut concepts = Arena::new();
        let mut roles = Arena::new();
        let mut concept_process_datas = Arena::<ConceptProcessData>::new();
        let mut concept_reference_linking_datas =
            Arena::<ConceptSaturationReferenceLinkingData>::new();
        let mut saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let role = roles.push(role_with_tag(7, false));
        roles.get_mut(role).add_indirect_super_role_linker(NegLink {
            target: role,
            negated: false,
        });
        let sub = concepts.push(concept_with_tag(CCSUB, 31, true));
        let mut reapply_some = concept_with_tag(CCSOME, 33, true);
        reapply_some.add_operand_linker(sub, false);
        let reapply_some = concepts.push(reapply_some);
        let mut reapply_con_des = ConceptDescriptor::new();
        reapply_con_des.concept = reapply_some;
        reapply_con_des.negated = true;
        let reapply_con_des = process_context.alloc_con_desc(reapply_con_des);
        let reapply = process_context.alloc_reapply_con_desc(ReapplyConceptDescriptor::new(
            reapply_con_des,
            TrackPointId::NONE,
            false,
        ));
        process_context.node_add_role_reapply_concept_descriptor(node, role, reapply);
        let mut some = concept_with_tag(CCSOME, 41, true);
        some.set_role(role);
        let some = concepts.push(some);
        let ext_ref = add_saturation_reference(&mut saturation_reference_linkings, ext_sat);
        let mut ext_ref_data = ConceptSaturationReferenceLinkingData::new();
        ext_ref_data.set_existential_successor_concept_saturation_reference_linking_data(ext_ref);
        attach_concept_reference_data(
            &mut concepts,
            some,
            &mut concept_process_datas,
            &mut concept_reference_linking_datas,
            ext_ref_data,
        );
        let con_sat_des = add_saturation_label_descriptor(
            &mut process_context,
            sat_label_set,
            &concepts,
            some,
            false,
            INVALID,
        );
        set_saturation_label_descriptor_linker(&mut process_context, sat_label_set, &[con_sat_des]);
        let mut dispatches = Vec::new();

        assert!(
            analyser.prepare_saturated_existentials_model_merge_dispatches(
                node,
                saturation_node,
                &concepts,
                &roles,
                &concept_process_datas,
                &concept_reference_linking_datas,
                &saturation_reference_linkings,
                &mut process_context,
                None,
                &mut dispatches,
            )
        );
        assert_eq!(dispatches.len(), 1);
        assert!(!analyser.test_saturated_existentials_model_mergable(
            node,
            saturation_node,
            &concepts,
            &roles,
            &concept_process_datas,
            &concept_reference_linking_datas,
            &saturation_reference_linkings,
            &mut process_context,
            None,
        ));
    }

    #[test]
    fn classification_message_analyser_subsumer_merged_saturated_wrapper_reports_clashed_merge() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let mut concepts = Arena::new();
        let roles = Arena::<Role>::new();
        let mut concept_process_datas = Arena::<ConceptProcessData>::new();
        let mut concept_reference_linking_datas =
            Arena::<ConceptSaturationReferenceLinkingData>::new();
        let mut saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let test_concept = concepts.push(concept_with_tag(CCATOM, 31, true));
        let (node, label_set) = add_completion_label_set_node(&mut process_context);
        let (sat_node, sat_label_set) = add_saturation_label_set_node(&mut process_context);
        let sat_ref = add_saturation_reference(&mut saturation_reference_linkings, sat_node);
        let mut ref_data = ConceptSaturationReferenceLinkingData::new();
        ref_data.set_saturation_reference_linking_data(sat_ref, false);
        attach_concept_reference_data(
            &mut concepts,
            test_concept,
            &mut concept_process_datas,
            &mut concept_reference_linking_datas,
            ref_data,
        );
        add_label_descriptor(
            &mut process_context,
            label_set,
            &concepts,
            test_concept,
            false,
            TrackPointId::NONE,
        );
        add_saturation_label_descriptor(
            &mut process_context,
            sat_label_set,
            &concepts,
            test_concept,
            true,
            INVALID,
        );
        let mut merge_satisfiable = true;
        let mut dispatches = Vec::new();

        assert!(
            analyser.prepare_subsumer_candidate_merged_saturated_model_dispatches(
                node,
                test_concept,
                false,
                &mut merge_satisfiable,
                &concepts,
                &roles,
                &concept_process_datas,
                &concept_reference_linking_datas,
                &saturation_reference_linkings,
                &mut process_context,
                None,
                &mut dispatches,
            )
        );

        assert!(!merge_satisfiable);
        assert!(dispatches.is_empty());
    }

    #[test]
    fn classification_message_analyser_subsumer_merged_saturated_wrapper_reaches_existential_dispatch(
    ) {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let (node, _) = add_completion_label_set_node(&mut process_context);
        let (saturation_node, sat_label_set) = add_saturation_label_set_node(&mut process_context);
        let ext_sat = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(13));
        let mut concepts = Arena::new();
        let mut roles = Arena::new();
        let mut concept_process_datas = Arena::<ConceptProcessData>::new();
        let mut concept_reference_linking_datas =
            Arena::<ConceptSaturationReferenceLinkingData>::new();
        let mut saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let test_concept = concepts.push(concept_with_tag(CCATOM, 29, true));
        let test_ref =
            add_saturation_reference(&mut saturation_reference_linkings, saturation_node);
        let mut test_ref_data = ConceptSaturationReferenceLinkingData::new();
        test_ref_data.set_saturation_reference_linking_data(test_ref, false);
        attach_concept_reference_data(
            &mut concepts,
            test_concept,
            &mut concept_process_datas,
            &mut concept_reference_linking_datas,
            test_ref_data,
        );
        let role = roles.push(role_with_tag(7, false));
        roles.get_mut(role).add_indirect_super_role_linker(NegLink {
            target: role,
            negated: false,
        });
        let sub = concepts.push(concept_with_tag(CCSUB, 31, true));
        let mut reapply_some = concept_with_tag(CCSOME, 33, true);
        reapply_some.add_operand_linker(sub, false);
        let reapply_some = concepts.push(reapply_some);
        let mut reapply_con_des = ConceptDescriptor::new();
        reapply_con_des.concept = reapply_some;
        reapply_con_des.negated = true;
        let reapply_con_des = process_context.alloc_con_desc(reapply_con_des);
        let reapply = process_context.alloc_reapply_con_desc(ReapplyConceptDescriptor::new(
            reapply_con_des,
            TrackPointId::NONE,
            false,
        ));
        process_context.node_add_role_reapply_concept_descriptor(node, role, reapply);
        let mut some = concept_with_tag(CCSOME, 41, true);
        some.set_role(role);
        let some = concepts.push(some);
        let ext_ref = add_saturation_reference(&mut saturation_reference_linkings, ext_sat);
        let mut ext_ref_data = ConceptSaturationReferenceLinkingData::new();
        ext_ref_data.set_existential_successor_concept_saturation_reference_linking_data(ext_ref);
        attach_concept_reference_data(
            &mut concepts,
            some,
            &mut concept_process_datas,
            &mut concept_reference_linking_datas,
            ext_ref_data,
        );
        let con_sat_des = add_saturation_label_descriptor(
            &mut process_context,
            sat_label_set,
            &concepts,
            some,
            false,
            INVALID,
        );
        set_saturation_label_descriptor_linker(&mut process_context, sat_label_set, &[con_sat_des]);
        let mut merge_satisfiable = false;
        let mut dispatches = Vec::new();

        assert!(
            analyser.prepare_subsumer_candidate_merged_saturated_model_dispatches(
                node,
                test_concept,
                false,
                &mut merge_satisfiable,
                &concepts,
                &roles,
                &concept_process_datas,
                &concept_reference_linking_datas,
                &saturation_reference_linkings,
                &mut process_context,
                None,
                &mut dispatches,
            )
        );

        assert!(merge_satisfiable);
        assert_eq!(dispatches.len(), 1);
        assert_eq!(dispatches[0].existential_sat_node, ext_sat);
        assert_eq!(
            dispatches[0].trivial_successor_propagated_concept_list,
            vec![(sub, true)]
        );
    }

    #[test]
    fn classification_message_analyser_subsumer_merged_saturated_live_executes_existential_probe() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let (node, _) = add_completion_label_set_node(&mut process_context);
        let (saturation_node, sat_label_set) = add_saturation_label_set_node(&mut process_context);
        let (ext_sat, ext_sat_label_set) = add_saturation_label_set_node(&mut process_context);
        let mut concepts = Arena::new();
        let mut roles = Arena::new();
        let mut concept_process_datas = Arena::<ConceptProcessData>::new();
        let mut concept_reference_linking_datas =
            Arena::<ConceptSaturationReferenceLinkingData>::new();
        let mut saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let test_concept = concepts.push(concept_with_tag(CCATOM, 29, true));
        let test_ref =
            add_saturation_reference(&mut saturation_reference_linkings, saturation_node);
        let mut test_ref_data = ConceptSaturationReferenceLinkingData::new();
        test_ref_data.set_saturation_reference_linking_data(test_ref, false);
        attach_concept_reference_data(
            &mut concepts,
            test_concept,
            &mut concept_process_datas,
            &mut concept_reference_linking_datas,
            test_ref_data,
        );
        let role = roles.push(role_with_tag(7, false));
        roles.get_mut(role).add_indirect_super_role_linker(NegLink {
            target: role,
            negated: false,
        });
        let sub = concepts.push(concept_with_tag(CCSUB, 31, true));
        add_saturation_label_descriptor(
            &mut process_context,
            ext_sat_label_set,
            &concepts,
            sub,
            true,
            INVALID,
        );
        let mut reapply_some = concept_with_tag(CCSOME, 33, true);
        reapply_some.add_operand_linker(sub, false);
        let reapply_some = concepts.push(reapply_some);
        let mut reapply_con_des = ConceptDescriptor::new();
        reapply_con_des.concept = reapply_some;
        reapply_con_des.negated = true;
        let reapply_con_des = process_context.alloc_con_desc(reapply_con_des);
        let reapply = process_context.alloc_reapply_con_desc(ReapplyConceptDescriptor::new(
            reapply_con_des,
            TrackPointId::NONE,
            false,
        ));
        process_context.node_add_role_reapply_concept_descriptor(node, role, reapply);
        let mut some = concept_with_tag(CCSOME, 41, true);
        some.set_role(role);
        let some = concepts.push(some);
        let ext_ref = add_saturation_reference(&mut saturation_reference_linkings, ext_sat);
        let mut ext_ref_data = ConceptSaturationReferenceLinkingData::new();
        ext_ref_data.set_existential_successor_concept_saturation_reference_linking_data(ext_ref);
        attach_concept_reference_data(
            &mut concepts,
            some,
            &mut concept_process_datas,
            &mut concept_reference_linking_datas,
            ext_ref_data,
        );
        let con_sat_des = add_saturation_label_descriptor(
            &mut process_context,
            sat_label_set,
            &concepts,
            some,
            false,
            INVALID,
        );
        set_saturation_label_descriptor_linker(&mut process_context, sat_label_set, &[con_sat_des]);
        let mut merge_satisfiable = false;

        assert!(
            analyser.test_subsumer_candidate_possible_with_merged_saturated_model(
                node,
                test_concept,
                false,
                &mut merge_satisfiable,
                &concepts,
                &roles,
                &concept_process_datas,
                &concept_reference_linking_datas,
                &saturation_reference_linkings,
                &mut process_context,
                None,
            )
        );
        assert!(merge_satisfiable);
    }

    #[test]
    fn classification_message_analyser_collects_live_equivalent_non_candidate_possible_subsumers() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let (node, label_set) = add_completion_label_set_node(&mut process_context);
        let mut ontology = OntologyArenas::new();
        let mut concepts = Arena::new();
        let roles = Arena::<Role>::new();
        let mut concept_process_datas = Arena::<ConceptProcessData>::new();
        let mut concept_reference_linking_datas =
            Arena::<ConceptSaturationReferenceLinkingData>::new();
        let mut saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let direct_non_candidate = concepts.push(concept_with_tag(CCATOM, 30, true));
        let filtered_operand = concepts.push(concept_with_tag(CCATOM, 40, true));
        let mut filtered_equivalence = concept_with_tag(CCEQ, 50, true);
        filtered_equivalence.add_operand_linker(filtered_operand, false);
        let filtered_equivalence = concepts.push(filtered_equivalence);
        let (sat_node, _) = add_saturation_label_set_node(&mut process_context);
        let sat_ref = add_saturation_reference(&mut saturation_reference_linkings, sat_node);
        let mut ref_data = ConceptSaturationReferenceLinkingData::new();
        ref_data.set_saturation_reference_linking_data(sat_ref, true);
        attach_concept_reference_data(
            &mut concepts,
            filtered_operand,
            &mut concept_process_datas,
            &mut concept_reference_linking_datas,
            ref_data,
        );
        add_label_descriptor(
            &mut process_context,
            label_set,
            &concepts,
            filtered_operand,
            true,
            TrackPointId::NONE,
        );
        ontology.insert_equivalent_concept_non_candidate(filtered_equivalence);
        ontology.insert_equivalent_concept_non_candidate(direct_non_candidate);

        let (set_exists, possible_subsumers) = analyser
            .collect_equivalent_non_candidate_possible_subsumers(
                node,
                &ontology,
                &concepts,
                &roles,
                &concept_process_datas,
                &concept_reference_linking_datas,
                &saturation_reference_linkings,
                &mut process_context,
                None,
            );

        assert!(set_exists);
        assert_eq!(possible_subsumers, vec![direct_non_candidate]);
    }

    #[test]
    fn classification_message_analyser_equivalence_alternatives_records_failed_merge() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let (node, _) = add_completion_label_set_node(&mut process_context);
        let mut concepts = Arena::new();
        let roles = Arena::<Role>::new();
        let concept_process_datas = Arena::<ConceptProcessData>::new();
        let concept_reference_linking_datas = Arena::<ConceptSaturationReferenceLinkingData>::new();
        let saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let concept = concepts.push(concept_with_tag(CCATOM, 31, true));
        let mut merge_hash = std::collections::HashMap::new();
        let mut one_satisfiable = false;
        let mut all_unsatisfiable = true;

        assert!(!analyser.test_equivalence_concept_alternatives(
            node,
            &[(concept, false)],
            &mut merge_hash,
            &mut one_satisfiable,
            &mut all_unsatisfiable,
            &concepts,
            &roles,
            &concept_process_datas,
            &concept_reference_linking_datas,
            &saturation_reference_linkings,
            &mut process_context,
            None,
        ));
        assert!(!one_satisfiable);
        assert!(!all_unsatisfiable);
        assert_eq!(
            merge_hash.get(&(concept, false)).copied(),
            Some(SaturatedMergedTestItem {
                successfully_merged: false,
                satisfiable_merged: false,
            })
        );
    }

    #[test]
    fn classification_message_analyser_equivalence_alternatives_accepts_all_unsatisfiable_merge() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let mut concepts = Arena::new();
        let roles = Arena::<Role>::new();
        let mut concept_process_datas = Arena::<ConceptProcessData>::new();
        let mut concept_reference_linking_datas =
            Arena::<ConceptSaturationReferenceLinkingData>::new();
        let mut saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let concept = concepts.push(concept_with_tag(CCATOM, 31, true));
        let (node, label_set) = add_completion_label_set_node(&mut process_context);
        let (sat_node, sat_label_set) = add_saturation_label_set_node(&mut process_context);
        let sat_ref = add_saturation_reference(&mut saturation_reference_linkings, sat_node);
        let mut ref_data = ConceptSaturationReferenceLinkingData::new();
        ref_data.set_saturation_reference_linking_data(sat_ref, false);
        attach_concept_reference_data(
            &mut concepts,
            concept,
            &mut concept_process_datas,
            &mut concept_reference_linking_datas,
            ref_data,
        );
        add_label_descriptor(
            &mut process_context,
            label_set,
            &concepts,
            concept,
            false,
            TrackPointId::NONE,
        );
        add_saturation_label_descriptor(
            &mut process_context,
            sat_label_set,
            &concepts,
            concept,
            true,
            INVALID,
        );
        let mut merge_hash = std::collections::HashMap::new();
        let mut one_satisfiable = false;
        let mut all_unsatisfiable = true;

        assert!(analyser.test_equivalence_concept_alternatives(
            node,
            &[(concept, false)],
            &mut merge_hash,
            &mut one_satisfiable,
            &mut all_unsatisfiable,
            &concepts,
            &roles,
            &concept_process_datas,
            &concept_reference_linking_datas,
            &saturation_reference_linkings,
            &mut process_context,
            None,
        ));
        assert!(!one_satisfiable);
        assert!(all_unsatisfiable);
        assert_eq!(
            merge_hash.get(&(concept, false)).copied(),
            Some(SaturatedMergedTestItem {
                successfully_merged: true,
                satisfiable_merged: false,
            })
        );
    }

    #[test]
    fn classification_message_analyser_collect_equivalence_expands_negated_and_to_existential() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let (node, _) = add_completion_label_set_node(&mut process_context);
        let mut concepts = Arena::new();
        let roles = Arena::<Role>::new();
        let concept_process_datas = Arena::<ConceptProcessData>::new();
        let concept_reference_linking_datas = Arena::<ConceptSaturationReferenceLinkingData>::new();
        let saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let some = concepts.push(concept_with_tag(CCSOME, 31, true));
        let mut conjunction = concept_with_tag(CCAND, 41, false);
        conjunction.add_operand_linker(some, true);
        let conjunction = concepts.push(conjunction);
        let mut alternatives = Vec::new();
        let mut merge_hash = std::collections::HashMap::new();
        let mut one_satisfiable = false;
        let mut all_unsatisfiable = true;

        assert!(!analyser.collect_equivalence_concept_alternatives(
            node,
            conjunction,
            true,
            &mut alternatives,
            &mut merge_hash,
            &mut one_satisfiable,
            &mut all_unsatisfiable,
            &concepts,
            &roles,
            &concept_process_datas,
            &concept_reference_linking_datas,
            &saturation_reference_linkings,
            &mut process_context,
            None,
        ));
        assert_eq!(alternatives, vec![(some, false)]);
        assert!(!one_satisfiable);
        assert!(!all_unsatisfiable);
        assert_eq!(
            merge_hash.get(&(some, false)).copied(),
            Some(SaturatedMergedTestItem {
                successfully_merged: false,
                satisfiable_merged: false,
            })
        );
    }

    #[test]
    fn classification_message_analyser_collect_equivalence_uses_cached_satisfiable_merge() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let (node, _) = add_completion_label_set_node(&mut process_context);
        let mut concepts = Arena::new();
        let roles = Arena::<Role>::new();
        let concept_process_datas = Arena::<ConceptProcessData>::new();
        let concept_reference_linking_datas = Arena::<ConceptSaturationReferenceLinkingData>::new();
        let saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let some = concepts.push(concept_with_tag(CCSOME, 31, true));
        let mut alternatives = Vec::new();
        let mut merge_hash = std::collections::HashMap::new();
        merge_hash.insert(
            (some, false),
            SaturatedMergedTestItem {
                successfully_merged: true,
                satisfiable_merged: true,
            },
        );
        let mut one_satisfiable = false;
        let mut all_unsatisfiable = true;

        assert!(analyser.collect_equivalence_concept_alternatives(
            node,
            some,
            false,
            &mut alternatives,
            &mut merge_hash,
            &mut one_satisfiable,
            &mut all_unsatisfiable,
            &concepts,
            &roles,
            &concept_process_datas,
            &concept_reference_linking_datas,
            &saturation_reference_linkings,
            &mut process_context,
            None,
        ));
        assert!(alternatives.is_empty());
        assert!(one_satisfiable);
        assert!(!all_unsatisfiable);
    }

    #[test]
    fn classification_message_analyser_collect_equivalence_label_hit_short_circuits() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let (node, label_set) = add_completion_label_set_node(&mut process_context);
        let mut concepts = Arena::new();
        let roles = Arena::<Role>::new();
        let concept_process_datas = Arena::<ConceptProcessData>::new();
        let concept_reference_linking_datas = Arena::<ConceptSaturationReferenceLinkingData>::new();
        let saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let concept = concepts.push(concept_with_tag(CCATOM, 31, true));
        add_label_descriptor(
            &mut process_context,
            label_set,
            &concepts,
            concept,
            false,
            TrackPointId::NONE,
        );
        let mut alternatives = Vec::new();
        let mut merge_hash = std::collections::HashMap::new();
        let mut one_satisfiable = false;
        let mut all_unsatisfiable = true;

        assert!(analyser.collect_equivalence_concept_alternatives(
            node,
            concept,
            false,
            &mut alternatives,
            &mut merge_hash,
            &mut one_satisfiable,
            &mut all_unsatisfiable,
            &concepts,
            &roles,
            &concept_process_datas,
            &concept_reference_linking_datas,
            &saturation_reference_linkings,
            &mut process_context,
            None,
        ));
        assert!(alternatives.is_empty());
        assert!(merge_hash.is_empty());
        assert!(one_satisfiable);
        assert!(!all_unsatisfiable);
    }

    #[test]
    fn classification_message_analyser_collect_equivalence_missing_atom_clears_all_flag() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let (node, _) = add_completion_label_set_node(&mut process_context);
        let mut concepts = Arena::new();
        let roles = Arena::<Role>::new();
        let concept_process_datas = Arena::<ConceptProcessData>::new();
        let concept_reference_linking_datas = Arena::<ConceptSaturationReferenceLinkingData>::new();
        let saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let concept = concepts.push(concept_with_tag(CCATOM, 31, true));
        let mut alternatives = Vec::new();
        let mut merge_hash = std::collections::HashMap::new();
        let mut one_satisfiable = false;
        let mut all_unsatisfiable = true;

        assert!(!analyser.collect_equivalence_concept_alternatives(
            node,
            concept,
            false,
            &mut alternatives,
            &mut merge_hash,
            &mut one_satisfiable,
            &mut all_unsatisfiable,
            &concepts,
            &roles,
            &concept_process_datas,
            &concept_reference_linking_datas,
            &saturation_reference_linkings,
            &mut process_context,
            None,
        ));
        assert!(alternatives.is_empty());
        assert!(merge_hash.is_empty());
        assert!(!one_satisfiable);
        assert!(!all_unsatisfiable);
    }

    #[test]
    fn classification_message_analyser_collect_equivalence_aqchoose_filters_by_operand_negation() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let (node, _) = add_completion_label_set_node(&mut process_context);
        let mut concepts = Arena::new();
        let roles = Arena::<Role>::new();
        let concept_process_datas = Arena::<ConceptProcessData>::new();
        let concept_reference_linking_datas = Arena::<ConceptSaturationReferenceLinkingData>::new();
        let saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let skipped_some = concepts.push(concept_with_tag(CCSOME, 31, true));
        let chosen_some = concepts.push(concept_with_tag(CCSOME, 37, true));
        let mut aqchoose = concept_with_tag(CCAQCHOOCE, 41, false);
        aqchoose.add_operand_linker(skipped_some, false);
        aqchoose.add_operand_linker(chosen_some, true);
        let aqchoose = concepts.push(aqchoose);
        let mut alternatives = Vec::new();
        let mut merge_hash = std::collections::HashMap::new();
        let mut one_satisfiable = false;
        let mut all_unsatisfiable = true;

        assert!(!analyser.collect_equivalence_concept_alternatives(
            node,
            aqchoose,
            true,
            &mut alternatives,
            &mut merge_hash,
            &mut one_satisfiable,
            &mut all_unsatisfiable,
            &concepts,
            &roles,
            &concept_process_datas,
            &concept_reference_linking_datas,
            &saturation_reference_linkings,
            &mut process_context,
            None,
        ));
        assert!(alternatives.is_empty());
        assert!(merge_hash.is_empty());
        assert!(!one_satisfiable);
        assert!(!all_unsatisfiable);
    }

    #[test]
    fn classification_message_analyser_model_clash_detects_deterministic_opposite_label() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let (node, label_set) = add_completion_label_set_node(&mut process_context);
        let mut concepts = Arena::new();
        let concept = concepts.push(concept_with_tag(CCATOM, 31, true));
        let deterministic_track = add_branch_track_point(&mut process_context, 0);
        add_label_descriptor(
            &mut process_context,
            label_set,
            &concepts,
            concept,
            true,
            deterministic_track,
        );

        let result = analyser.check_can_have_clash_with_model(
            node,
            concept,
            false,
            0,
            &mut std::collections::HashSet::new(),
            NodeId::NONE,
            &concepts,
            &process_context,
        );
        assert_eq!(
            result,
            ModelClashCheckResult {
                clash_found: true,
                unknown: false,
                clash_free: false,
            }
        );
    }

    #[test]
    fn classification_message_analyser_model_clash_treats_nondeterministic_opposite_label_unknown()
    {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let (node, label_set) = add_completion_label_set_node(&mut process_context);
        let mut concepts = Arena::new();
        let concept = concepts.push(concept_with_tag(CCATOM, 31, true));
        let nondeterministic_track = add_branch_track_point(&mut process_context, 3);
        add_label_descriptor(
            &mut process_context,
            label_set,
            &concepts,
            concept,
            true,
            nondeterministic_track,
        );

        let result = analyser.check_can_have_clash_with_model(
            node,
            concept,
            false,
            0,
            &mut std::collections::HashSet::new(),
            NodeId::NONE,
            &concepts,
            &process_context,
        );
        assert_eq!(
            result,
            ModelClashCheckResult {
                clash_found: false,
                unknown: true,
                clash_free: false,
            }
        );
    }

    #[test]
    fn classification_message_analyser_model_clash_same_label_is_clash_free() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let (node, label_set) = add_completion_label_set_node(&mut process_context);
        let mut concepts = Arena::new();
        let concept = concepts.push(concept_with_tag(CCATOM, 31, true));
        add_label_descriptor(
            &mut process_context,
            label_set,
            &concepts,
            concept,
            false,
            TrackPointId::NONE,
        );

        let result = analyser.check_can_have_clash_with_model(
            node,
            concept,
            false,
            0,
            &mut std::collections::HashSet::new(),
            NodeId::NONE,
            &concepts,
            &process_context,
        );
        assert_eq!(
            result,
            ModelClashCheckResult {
                clash_found: false,
                unknown: false,
                clash_free: true,
            }
        );
    }

    #[test]
    fn classification_message_analyser_model_clash_negated_and_requires_all_operand_clashes() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let (node, label_set) = add_completion_label_set_node(&mut process_context);
        let mut concepts = Arena::new();
        let op_a = concepts.push(concept_with_tag(CCATOM, 31, true));
        let op_b = concepts.push(concept_with_tag(CCATOM, 37, true));
        let mut conjunction = concept_with_tag(CCAND, 41, false);
        conjunction.add_operand_linker(op_a, false);
        conjunction.add_operand_linker(op_b, false);
        let conjunction = concepts.push(conjunction);
        let deterministic_track = add_branch_track_point(&mut process_context, 0);
        add_label_descriptor(
            &mut process_context,
            label_set,
            &concepts,
            op_a,
            false,
            deterministic_track,
        );
        add_label_descriptor(
            &mut process_context,
            label_set,
            &concepts,
            op_b,
            false,
            deterministic_track,
        );

        let result = analyser.check_can_have_clash_with_model(
            node,
            conjunction,
            true,
            0,
            &mut std::collections::HashSet::new(),
            NodeId::NONE,
            &concepts,
            &process_context,
        );
        assert!(result.clash_found);
        assert!(!result.unknown);
        assert!(!result.clash_free);
    }

    #[test]
    fn classification_message_analyser_model_clash_role_successor_clash_makes_all_clash_free() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let (node, _) = add_completion_label_set_node(&mut process_context);
        let (successor, successor_label_set) = add_completion_label_set_node(&mut process_context);
        let mut concepts = Arena::new();
        let mut roles = Arena::new();
        let role = roles.push(role_with_tag(7, false));
        let operand = concepts.push(concept_with_tag(CCATOM, 31, true));
        let mut all = concept_with_tag(CCALL, 41, false);
        all.set_role(role).add_operand_linker(operand, false);
        let all = concepts.push(all);
        let deterministic_track = add_branch_track_point(&mut process_context, 0);
        add_label_descriptor(
            &mut process_context,
            successor_label_set,
            &concepts,
            operand,
            true,
            deterministic_track,
        );
        add_role_link(
            &mut process_context,
            node,
            successor,
            role,
            deterministic_track,
        );

        let result = analyser.check_can_have_clash_with_model(
            node,
            all,
            false,
            0,
            &mut std::collections::HashSet::new(),
            NodeId::NONE,
            &concepts,
            &process_context,
        );
        assert!(!result.clash_found);
        assert!(!result.unknown);
        assert!(result.clash_free);
    }

    #[test]
    fn classification_message_analyser_model_clash_depth_guard_returns_unknown() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let (node, _) = add_completion_label_set_node(&mut process_context);
        let mut concepts = Arena::new();
        let concept = concepts.push(concept_with_tag(CCATOM, 31, true));

        let result = analyser.check_can_have_clash_with_model(
            node,
            concept,
            false,
            6,
            &mut std::collections::HashSet::new(),
            NodeId::NONE,
            &concepts,
            &process_context,
        );
        assert!(!result.clash_found);
        assert!(result.unknown);
        assert!(!result.clash_free);
    }

    #[test]
    fn linked_role_saturation_successor_hash_lazy_create_gets_role_bucket() {
        let mut process_context = ProcessContext::new();
        let sat_node = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(11));
        let role = RoleId::new(7);

        assert!(process_context
            .sat_node_ext_linked_role_successor_hash(sat_node, false)
            .is_none());
        let hash = process_context.sat_node_ext_linked_role_successor_hash(sat_node, true);
        assert!(hash.is_some());
        assert_eq!(
            process_context.sat_node_ext_linked_role_successor_hash(sat_node, false),
            hash
        );
        assert!(process_context
            .linked_role_successor_data(hash, role, false)
            .is_none());
        let role_data = process_context.linked_role_successor_data(hash, role, true);
        assert!(role_data.is_some());
        assert_eq!(
            process_context.linked_role_successor_data(hash, role, false),
            role_data
        );
        assert!(process_context
            .linked_role_sat_succ_hash(hash)
            .has_linked_role_successor_data(role));
        assert!(process_context
            .linked_role_sat_succ_hash(hash)
            .get_linked_role_successor_data(RoleId::new(9))
            .is_none());
    }

    #[test]
    fn linked_role_saturation_successor_data_reports_active_successor() {
        let mut process_context = ProcessContext::new();
        let sat_node = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(11));
        let active_successor =
            process_context.alloc_sat_node(IndividualSaturationProcessNode::new(13));
        let inactive_successor =
            process_context.alloc_sat_node(IndividualSaturationProcessNode::new(17));
        process_context.sat_node_mut(sat_node).set_individual_id(11);
        process_context
            .sat_node_mut(active_successor)
            .set_individual_id(13);
        process_context
            .sat_node_mut(inactive_successor)
            .set_individual_id(17);
        let role = RoleId::new(7);
        let hash = process_context.sat_node_ext_linked_role_successor_hash(sat_node, true);
        let role_data = process_context.linked_role_successor_data(hash, role, true);
        let mut active_data = SaturationSuccessorData::new();
        active_data
            .set_successor_individual_node(active_successor)
            .set_successor_count(1)
            .set_active_count(1);
        let active_data = process_context.alloc_sat_succ_data(active_data);
        let mut inactive_data = SaturationSuccessorData::new();
        inactive_data
            .set_successor_individual_node(inactive_successor)
            .set_successor_count(1)
            .set_active_count(0);
        let inactive_data = process_context.alloc_sat_succ_data(inactive_data);
        let active_successor_id = process_context
            .sat_node(active_successor)
            .get_individual_id();
        let inactive_successor_id = process_context
            .sat_node(inactive_successor)
            .get_individual_id();
        process_context
            .linked_role_sat_succ_data_mut(role_data)
            .get_successor_node_data_map_mut()
            .insert(active_successor_id, active_data);
        process_context
            .linked_role_sat_succ_data_mut(role_data)
            .get_successor_node_data_map_mut()
            .insert(inactive_successor_id, inactive_data);
        process_context
            .linked_role_sat_succ_data_mut(role_data)
            .set_last_successor_link_data(active_data)
            .set_successor_count(2);

        assert!(
            process_context.linked_role_successor_has_active_successor(role_data, active_successor)
        );
        assert!(!process_context
            .linked_role_successor_has_active_successor(role_data, inactive_successor));
        assert!(!process_context
            .linked_role_successor_has_active_successor(role_data, SatNodeId::new(99)));
        assert_eq!(
            process_context
                .linked_role_sat_succ_data(role_data)
                .get_last_successor_link_data(),
            active_data
        );
        assert_eq!(
            process_context
                .linked_role_sat_succ_data(role_data)
                .get_successor_count(),
            2
        );
    }

    #[test]
    fn classification_message_analyser_saturated_merge_gate_requires_completed_clean_node() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let incomplete = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(11));
        let insufficient = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(13));
        let nominal_connection =
            process_context.alloc_sat_node(IndividualSaturationProcessNode::new(17));
        let cardinality_problematic =
            process_context.alloc_sat_node(IndividualSaturationProcessNode::new(19));
        let clean = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(23));

        process_context
            .sat_node_mut(insufficient)
            .set_completed(true);
        process_context
            .sat_node_mut(insufficient)
            .indirect_status_flags
            .add_flags_code(IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT);
        process_context
            .sat_node_mut(nominal_connection)
            .set_completed(true);
        process_context
            .sat_node_mut(nominal_connection)
            .indirect_status_flags
            .add_flags_code(
                IndividualSaturationProcessNodeStatusFlags::INDSATFLAGNOMINALCONNECTION,
            );
        process_context
            .sat_node_mut(cardinality_problematic)
            .set_completed(true);
        process_context
            .sat_node_mut(cardinality_problematic)
            .indirect_status_flags
            .add_flags_code(
                IndividualSaturationProcessNodeStatusFlags::INDSATFLAGCARDINALITYPROPLEMATIC,
            );
        process_context.sat_node_mut(clean).set_completed(true);

        assert!(!analyser
            .is_saturated_individual_node_merge_test_eligible(&process_context, incomplete));
        assert!(!analyser
            .is_saturated_individual_node_merge_test_eligible(&process_context, insufficient));
        assert!(!analyser.is_saturated_individual_node_merge_test_eligible(
            &process_context,
            nominal_connection
        ));
        assert!(!analyser.is_saturated_individual_node_merge_test_eligible(
            &process_context,
            cardinality_problematic
        ));
        assert!(analyser.is_saturated_individual_node_merge_test_eligible(&process_context, clean));
        assert!(!analyser.is_saturated_individual_node_merge_test_eligible(
            &process_context,
            SatNodeId::new(999)
        ));
    }

    #[test]
    fn classification_message_analyser_resolves_only_merge_eligible_saturated_node_for_concept() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let sat_node = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(11));
        process_context.sat_node_mut(sat_node).set_completed(true);

        let mut concepts = Arena::new();
        let mut concept_process_datas = Arena::<ConceptProcessData>::new();
        let mut concept_reference_linking_datas =
            Arena::<ConceptSaturationReferenceLinkingData>::new();
        let mut saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let sat_ref = {
            let mut linking = SaturationConceptReferenceLinking::new();
            linking.set_individual_process_node_for_concept(sat_node);
            saturation_reference_linkings.push(linking)
        };
        let con_ref = {
            let mut data = ConceptSaturationReferenceLinkingData::new();
            data.set_saturation_reference_linking_data(sat_ref, false);
            concept_reference_linking_datas.push(data)
        };
        let con_proc = {
            let mut data = ConceptProcessData::new();
            data.set_concept_reference_linking(con_ref);
            concept_process_datas.push(data)
        };
        let mut concept_data = concept_with_tag(CCATOM, 31, true);
        concept_data.set_concept_data(con_proc.raw);
        let concept = concepts.push(concept_data);

        assert_eq!(
            analyser.get_merge_test_eligible_saturated_individual_node_for_concept(
                concept,
                false,
                &concepts,
                &concept_process_datas,
                &concept_reference_linking_datas,
                &saturation_reference_linkings,
                &process_context,
            ),
            Some(sat_node)
        );

        process_context
            .sat_node_mut(sat_node)
            .indirect_status_flags
            .add_flags_code(IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT);
        assert_eq!(
            analyser.get_merge_test_eligible_saturated_individual_node_for_concept(
                concept,
                false,
                &concepts,
                &concept_process_datas,
                &concept_reference_linking_datas,
                &saturation_reference_linkings,
                &process_context,
            ),
            None
        );
    }

    #[test]
    fn classification_message_analyser_concept_set_merge_requires_both_label_sets() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let node = process_context.alloc_node(IndividualProcessNode::new(ProcessContextId::NONE));
        let sat_node = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(11));

        assert_eq!(
            analyser.test_concept_set_with_saturated_model_mergable(
                &process_context,
                node,
                sat_node
            ),
            SaturatedConceptSetMergeResult {
                mergable: false,
                clashed: false
            }
        );
    }

    #[test]
    fn classification_message_analyser_concept_set_merge_reports_saturated_clash_flag() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let (node, _) = add_completion_label_set_node(&mut process_context);
        let (sat_node, _) = add_saturation_label_set_node(&mut process_context);
        process_context
            .sat_node_mut(sat_node)
            .indirect_status_flags
            .add_flags_code(IndividualSaturationProcessNodeStatusFlags::INDSATFLAGCLASHED);

        assert_eq!(
            analyser.test_concept_set_with_saturated_model_mergable(
                &process_context,
                node,
                sat_node
            ),
            SaturatedConceptSetMergeResult {
                mergable: true,
                clashed: true
            }
        );
    }

    #[test]
    fn classification_message_analyser_concept_set_merge_detects_descriptor_polarity_clash() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let mut concepts = Arena::new();
        let concept = concepts.push(concept_with_tag(CCATOM, 31, true));
        let (node, label_set) = add_completion_label_set_node(&mut process_context);
        let (sat_node, sat_label_set) = add_saturation_label_set_node(&mut process_context);
        add_label_descriptor(
            &mut process_context,
            label_set,
            &concepts,
            concept,
            false,
            TrackPointId::NONE,
        );
        add_saturation_label_descriptor(
            &mut process_context,
            sat_label_set,
            &concepts,
            concept,
            true,
            INVALID,
        );

        assert_eq!(
            analyser.test_concept_set_with_saturated_model_mergable(
                &process_context,
                node,
                sat_node
            ),
            SaturatedConceptSetMergeResult {
                mergable: true,
                clashed: true
            }
        );
    }

    #[test]
    fn classification_message_analyser_concept_set_merge_rejects_positive_descriptor_with_saturated_reapply(
    ) {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let mut concepts = Arena::new();
        let concept = concepts.push(concept_with_tag(CCATOM, 31, true));
        let (node, label_set) = add_completion_label_set_node(&mut process_context);
        let (sat_node, sat_label_set) = add_saturation_label_set_node(&mut process_context);
        add_label_descriptor(
            &mut process_context,
            label_set,
            &concepts,
            concept,
            false,
            TrackPointId::NONE,
        );
        process_context
            .reapply_con_sat_label_set_mut(sat_label_set)
            .concept_des_dep_hash
            .insert(
                concepts.get(concept).get_concept_tag(),
                ConceptSaturationDescriptorReapplyData {
                    con_sat_des: super::super::super::saturation::satellites::ConceptSaturationDescriptorId::NONE,
                    imp_reapply_con_sat_des: super::super::super::saturation::satellites::ImplicationReapplyConceptSaturationDescriptorId::new(77),
                },
            );

        assert_eq!(
            analyser.test_concept_set_with_saturated_model_mergable(
                &process_context,
                node,
                sat_node
            ),
            SaturatedConceptSetMergeResult {
                mergable: false,
                clashed: false
            }
        );
    }

    #[test]
    fn classification_message_analyser_concept_set_merge_rejects_positive_saturated_descriptor_with_non_empty_reapply_queue(
    ) {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let mut concepts = Arena::new();
        let concept = concepts.push(concept_with_tag(CCATOM, 31, true));
        let (node, label_set) = add_completion_label_set_node(&mut process_context);
        let (sat_node, sat_label_set) = add_saturation_label_set_node(&mut process_context);
        let queue_head = process_context.alloc_cond_reapply_con_desc(
            super::super::super::process::reapply_sat::CondensedReapplyConceptDescriptor::new(
                ConDescId::NONE,
                TrackPointId::NONE,
                true,
            ),
        );
        let mut queue = CondensedReapplyQueue::new();
        queue.set_dynamic_pos_neg_reapply_des_linker(queue_head);
        process_context
            .label_set_mut(label_set)
            .concept_des_dep_map
            .insert(
                concepts.get(concept).get_concept_tag(),
                ConceptDescriptorDependencyReapplyData {
                    concept_descriptor: ConDescId::NONE,
                    pos_neg_reapply_queue: queue,
                },
            );
        add_saturation_label_descriptor(
            &mut process_context,
            sat_label_set,
            &concepts,
            concept,
            false,
            INVALID,
        );

        assert_eq!(
            analyser.test_concept_set_with_saturated_model_mergable(
                &process_context,
                node,
                sat_node
            ),
            SaturatedConceptSetMergeResult {
                mergable: false,
                clashed: false
            }
        );
    }

    #[test]
    fn classification_message_analyser_concept_set_merge_accepts_matching_labels() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let mut concepts = Arena::new();
        let concept = concepts.push(concept_with_tag(CCATOM, 31, true));
        let (node, label_set) = add_completion_label_set_node(&mut process_context);
        let (sat_node, sat_label_set) = add_saturation_label_set_node(&mut process_context);
        add_label_descriptor(
            &mut process_context,
            label_set,
            &concepts,
            concept,
            false,
            TrackPointId::NONE,
        );
        add_saturation_label_descriptor(
            &mut process_context,
            sat_label_set,
            &concepts,
            concept,
            false,
            INVALID,
        );

        assert_eq!(
            analyser.test_concept_set_with_saturated_model_mergable(
                &process_context,
                node,
                sat_node
            ),
            SaturatedConceptSetMergeResult {
                mergable: true,
                clashed: false
            }
        );
    }

    #[test]
    fn classification_message_analyser_role_successor_merge_is_vacuously_true_without_hashes() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let concepts = Arena::new();
        let node = process_context.alloc_node(IndividualProcessNode::new(ProcessContextId::NONE));
        let sat_node = process_context.alloc_sat_node(IndividualSaturationProcessNode::new(11));

        assert!(analyser.test_role_successors_with_saturated_model_mergable(
            &process_context,
            &concepts,
            node,
            sat_node
        ));
    }

    #[test]
    fn classification_message_analyser_role_successor_merge_rejects_missing_successor_operand() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let mut concepts = Arena::new();
        let operand = concepts.push(concept_with_tag(CCATOM, 41, true));
        let mut trigger = concept_with_tag(CCALL, 31, true);
        trigger.add_operand_linker(operand, true);
        let trigger = concepts.push(trigger);
        let role = RoleId::new(5);
        let (node, _) = add_completion_label_set_node(&mut process_context);
        let (succ_node, _) = add_completion_label_set_node(&mut process_context);
        add_role_link(
            &mut process_context,
            node,
            succ_node,
            role,
            TrackPointId::NONE,
        );
        let (sat_node, _) = add_saturation_label_set_node(&mut process_context);
        let con_sat_des = add_saturation_concept_descriptor(&mut process_context, trigger, false);
        add_backward_reapply_for_role(&mut process_context, sat_node, role, con_sat_des);

        assert!(
            !analyser.test_role_successors_with_saturated_model_mergable(
                &process_context,
                &concepts,
                node,
                sat_node
            )
        );
    }

    #[test]
    fn classification_message_analyser_role_successor_merge_accepts_satisfied_successor_operand() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let mut concepts = Arena::new();
        let operand = concepts.push(concept_with_tag(CCATOM, 41, true));
        let mut trigger = concept_with_tag(CCALL, 31, true);
        trigger.add_operand_linker(operand, true);
        let trigger = concepts.push(trigger);
        let role = RoleId::new(5);
        let (node, _) = add_completion_label_set_node(&mut process_context);
        let (succ_node, succ_label_set) = add_completion_label_set_node(&mut process_context);
        add_label_descriptor(
            &mut process_context,
            succ_label_set,
            &concepts,
            operand,
            false,
            TrackPointId::NONE,
        );
        add_role_link(
            &mut process_context,
            node,
            succ_node,
            role,
            TrackPointId::NONE,
        );
        let (sat_node, _) = add_saturation_label_set_node(&mut process_context);
        let con_sat_des = add_saturation_concept_descriptor(&mut process_context, trigger, false);
        add_backward_reapply_for_role(&mut process_context, sat_node, role, con_sat_des);

        assert!(analyser.test_role_successors_with_saturated_model_mergable(
            &process_context,
            &concepts,
            node,
            sat_node
        ));
    }

    #[test]
    fn classification_message_analyser_role_successor_merge_skips_when_root_has_reapply_concept() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let mut concepts = Arena::new();
        let operand = concepts.push(concept_with_tag(CCATOM, 41, true));
        let mut trigger = concept_with_tag(CCALL, 31, true);
        trigger.add_operand_linker(operand, true);
        let trigger = concepts.push(trigger);
        let role = RoleId::new(5);
        let (node, label_set) = add_completion_label_set_node(&mut process_context);
        add_label_descriptor(
            &mut process_context,
            label_set,
            &concepts,
            trigger,
            false,
            TrackPointId::NONE,
        );
        let (succ_node, _) = add_completion_label_set_node(&mut process_context);
        add_role_link(
            &mut process_context,
            node,
            succ_node,
            role,
            TrackPointId::NONE,
        );
        let (sat_node, _) = add_saturation_label_set_node(&mut process_context);
        let con_sat_des = add_saturation_concept_descriptor(&mut process_context, trigger, false);
        add_backward_reapply_for_role(&mut process_context, sat_node, role, con_sat_des);

        assert!(analyser.test_role_successors_with_saturated_model_mergable(
            &process_context,
            &concepts,
            node,
            sat_node
        ));
    }

    #[test]
    fn classification_message_analyser_delivers_merged_linkers_in_cpp_order() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let subsum = ClassificationMessageDataLinker::from_message(
            ClassificationMessageDataPayload::Header(ClassificationMessageData::new(
                ClassificationMessageDataType::TellClassSubsumption,
            )),
        );
        let pm = ClassificationMessageDataLinker::from_message(
            ClassificationMessageDataPayload::Header(ClassificationMessageData::new(
                ClassificationMessageDataType::TellClassPseudoModelIdentifiers,
            )),
        );
        let poss = ClassificationMessageDataLinker::from_message(
            ClassificationMessageDataPayload::Header(ClassificationMessageData::new(
                ClassificationMessageDataType::TellClassUpdatePossibleSubsumption,
            )),
        );
        let adapter = SatisfiableTaskClassificationMessageAdapter::new_with_handles(
            ConceptId::new(7),
            19,
            23,
            std::collections::HashMap::new(),
            0,
        );
        let mut observer = RecordingClassificationMessageDataObserver::new();

        let result = analyser.deliver_merged_classification_message_data(
            &adapter,
            Some(subsum),
            Some(pm),
            Some(poss),
            29,
            Some(&mut observer),
        );

        assert_eq!(
            result,
            ClassificationAnalyserMessageOutputResult {
                had_message_data: true,
                delivered_to_observer: true,
                released_memory_pool: None,
            }
        );
        assert_eq!(observer.get_told_messages().len(), 1);
        assert_eq!(observer.get_told_messages()[0].0, 19);
        assert_eq!(observer.get_told_messages()[0].2, 29);
        assert_eq!(
            observer.get_told_messages()[0].1.message_types(),
            vec![
                ClassificationMessageDataType::TellClassUpdatePossibleSubsumption,
                ClassificationMessageDataType::TellClassPseudoModelIdentifiers,
                ClassificationMessageDataType::TellClassSubsumption,
            ]
        );
    }

    #[test]
    fn classification_message_analyser_final_output_records_release_branch_without_messages() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let adapter = SatisfiableTaskClassificationMessageAdapter::new_with_handles(
            ConceptId::new(7),
            19,
            23,
            std::collections::HashMap::new(),
            0,
        );
        let mut observer = RecordingClassificationMessageDataObserver::new();

        let result = analyser.deliver_merged_classification_message_data(
            &adapter,
            None,
            None,
            None,
            31,
            Some(&mut observer),
        );

        assert_eq!(
            result,
            ClassificationAnalyserMessageOutputResult {
                had_message_data: false,
                delivered_to_observer: false,
                released_memory_pool: Some(31),
            }
        );
        assert!(observer.get_told_messages().is_empty());
    }

    #[test]
    fn classification_message_analyser_final_output_does_not_release_when_delivery_is_missing_observer(
    ) {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let subsum = ClassificationMessageDataLinker::from_message(
            ClassificationMessageDataPayload::Header(ClassificationMessageData::new(
                ClassificationMessageDataType::TellClassSubsumption,
            )),
        );
        let adapter = SatisfiableTaskClassificationMessageAdapter::new_with_handles(
            ConceptId::new(7),
            19,
            INVALID,
            std::collections::HashMap::new(),
            0,
        );
        let no_observer: Option<&mut RecordingClassificationMessageDataObserver> = None;

        let result = analyser.deliver_merged_classification_message_data(
            &adapter,
            Some(subsum),
            None,
            None,
            37,
            no_observer,
        );

        assert_eq!(
            result,
            ClassificationAnalyserMessageOutputResult {
                had_message_data: true,
                delivered_to_observer: false,
                released_memory_pool: None,
            }
        );
    }

    #[test]
    fn classification_message_analyser_creates_root_class_subsumption_message() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut concepts = Arena::new();
        let testing_concept = concepts.push(concept_with_tag(CCATOM, 10, true));
        let deterministic_subsumer = concepts.push(concept_with_tag(CCATOM, 20, true));
        let nondeterministic_subsumer = concepts.push(concept_with_tag(CCATOM, 30, true));
        let negated_subsumer = concepts.push(concept_with_tag(CCATOM, 40, true));
        let top_tag_concept = concepts.push(concept_with_tag(CCATOM, 1, true));
        let unnamed_concept = concepts.push(concept_with_tag(CCATOM, 50, false));
        let adapter = SatisfiableTaskClassificationMessageAdapter::new(
            testing_concept,
            EFEXTRACTSUBSUMERSROOTNODE,
        );

        let message = analyser
            .create_root_class_subsumption_message(
                &adapter,
                &[
                    ClassificationAnalyserConceptLabel::new(
                        nondeterministic_subsumer,
                        false,
                        Some(9),
                    ),
                    ClassificationAnalyserConceptLabel::new(deterministic_subsumer, false, Some(3)),
                    ClassificationAnalyserConceptLabel::new(negated_subsumer, true, Some(3)),
                    ClassificationAnalyserConceptLabel::new(top_tag_concept, false, Some(3)),
                    ClassificationAnalyserConceptLabel::new(unnamed_concept, false, Some(3)),
                    ClassificationAnalyserConceptLabel::new(testing_concept, false, Some(3)),
                ],
                5,
                &concepts,
            )
            .expect("root class subsumption message");

        assert_eq!(message.get_subsumed_concept(), testing_concept);
        assert_eq!(
            message.get_class_subsumer_list(),
            Some([deterministic_subsumer].as_slice())
        );
    }

    #[test]
    fn classification_message_analyser_creates_root_class_message_with_null_subsumer_list() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut concepts = Arena::new();
        let testing_concept = concepts.push(concept_with_tag(CCATOM, 10, true));
        let adapter = SatisfiableTaskClassificationMessageAdapter::new(
            testing_concept,
            EFEXTRACTSUBSUMERSROOTNODE,
        );

        let message = analyser
            .create_root_class_subsumption_message(&adapter, &[], 5, &concepts)
            .expect("root class subsumption message");

        assert_eq!(message.get_subsumed_concept(), testing_concept);
        assert!(message.get_class_subsumer_list().is_none());
    }

    #[test]
    fn classification_message_analyser_creates_other_node_class_subsumption_message() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut concepts = Arena::new();
        let analyse_concept = concepts.push(concept_with_tag(CCATOM, 10, true));
        let exact_subsumer = concepts.push(concept_with_tag(CCATOM, 20, true));
        let later_branch_concept = concepts.push(concept_with_tag(CCATOM, 30, true));
        let negated_exact = concepts.push(concept_with_tag(CCATOM, 40, true));
        let adapter = SatisfiableTaskClassificationMessageAdapter::new(
            analyse_concept,
            EFEXTRACTSUBSUMERSOTHERNODES,
        );

        let message = analyser
            .create_other_node_class_subsumption_message(
                &adapter,
                analyse_concept,
                7,
                true,
                &[
                    ClassificationAnalyserConceptLabel::new(exact_subsumer, false, Some(7)),
                    ClassificationAnalyserConceptLabel::new(later_branch_concept, false, Some(9)),
                    ClassificationAnalyserConceptLabel::new(negated_exact, true, Some(7)),
                    ClassificationAnalyserConceptLabel::new(analyse_concept, false, Some(7)),
                ],
                &concepts,
            )
            .expect("other-node class subsumption message");

        assert_eq!(message.get_subsumed_concept(), analyse_concept);
        assert_eq!(
            message.get_class_subsumer_list(),
            Some([exact_subsumer].as_slice())
        );
    }

    #[test]
    fn classification_message_analyser_other_node_branch_error_suppresses_message() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut concepts = Arena::new();
        let analyse_concept = concepts.push(concept_with_tag(CCATOM, 10, true));
        let lower_branch_concept = concepts.push(concept_with_tag(CCATOM, 20, true));
        let exact_subsumer = concepts.push(concept_with_tag(CCATOM, 30, true));
        let adapter = SatisfiableTaskClassificationMessageAdapter::new(
            analyse_concept,
            EFEXTRACTSUBSUMERSOTHERNODES,
        );

        assert!(analyser
            .create_other_node_class_subsumption_message(
                &adapter,
                analyse_concept,
                7,
                true,
                &[
                    ClassificationAnalyserConceptLabel::new(lower_branch_concept, false, Some(3)),
                    ClassificationAnalyserConceptLabel::new(exact_subsumer, false, Some(7)),
                ],
                &concepts,
            )
            .is_none());
    }

    #[test]
    fn classification_message_analyser_other_node_requires_single_dependency_descriptor() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut concepts = Arena::new();
        let analyse_concept = concepts.push(concept_with_tag(CCATOM, 10, true));
        let exact_subsumer = concepts.push(concept_with_tag(CCATOM, 20, true));
        let adapter = SatisfiableTaskClassificationMessageAdapter::new(
            analyse_concept,
            EFEXTRACTSUBSUMERSOTHERNODES,
        );

        assert!(analyser
            .create_other_node_class_subsumption_message(
                &adapter,
                analyse_concept,
                7,
                false,
                &[ClassificationAnalyserConceptLabel::new(
                    exact_subsumer,
                    false,
                    Some(7),
                )],
                &concepts,
            )
            .is_none());
    }

    #[test]
    fn classification_message_analyser_other_node_selection_records_analysed_concept() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut concepts = Arena::new();
        let testing_concept = concepts.push(concept_with_tag(CCATOM, 10, true));
        let analyse_concept = concepts.push(concept_with_tag(CCATOM, 20, true));
        let mut analysed_concepts = std::collections::HashSet::new();

        let candidate = analyser
            .select_other_node_analyse_candidate(
                testing_concept,
                ClassificationAnalyserConceptLabel::new(analyse_concept, false, Some(17)),
                true,
                &mut analysed_concepts,
                &concepts,
            )
            .expect("other-node analyse candidate");

        assert_eq!(
            candidate,
            ClassificationAnalyserOtherNodeCandidate {
                analyse_concept,
                analyse_branch_tag: 17,
            }
        );
        assert!(analysed_concepts.contains(&analyse_concept));
        assert!(analyser
            .select_other_node_analyse_candidate(
                testing_concept,
                ClassificationAnalyserConceptLabel::new(analyse_concept, false, Some(17)),
                true,
                &mut analysed_concepts,
                &concepts,
            )
            .is_none());
    }

    #[test]
    fn classification_message_analyser_other_node_selection_preserves_cpp_filters() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut concepts = Arena::new();
        let testing_concept = concepts.push(concept_with_tag(CCATOM, 10, true));
        let tag_one = concepts.push(concept_with_tag(CCATOM, 1, true));
        let negated = concepts.push(concept_with_tag(CCATOM, 20, true));
        let unnamed = concepts.push(concept_with_tag(CCATOM, 30, false));
        let no_info_required = concepts.push(concept_with_tag(CCATOM, 40, true));
        let no_dependency = concepts.push(concept_with_tag(CCATOM, 50, true));

        for (label, info_required) in [
            (
                ClassificationAnalyserConceptLabel::new(testing_concept, false, Some(3)),
                true,
            ),
            (
                ClassificationAnalyserConceptLabel::new(tag_one, false, Some(3)),
                true,
            ),
            (
                ClassificationAnalyserConceptLabel::new(negated, true, Some(3)),
                true,
            ),
            (
                ClassificationAnalyserConceptLabel::new(unnamed, false, Some(3)),
                true,
            ),
            (
                ClassificationAnalyserConceptLabel::new(no_info_required, false, Some(3)),
                false,
            ),
            (
                ClassificationAnalyserConceptLabel::new(no_dependency, false, None),
                true,
            ),
        ] {
            let mut analysed_concepts = std::collections::HashSet::new();
            assert!(analyser
                .select_other_node_analyse_candidate(
                    testing_concept,
                    label,
                    info_required,
                    &mut analysed_concepts,
                    &concepts,
                )
                .is_none());
            assert!(analysed_concepts.is_empty());
        }
    }

    #[test]
    fn classification_message_analyser_other_node_guard_skips_nominal_and_blocker_nodes() {
        let mut concepts = Arena::new();
        let testing_concept = concepts.push(concept_with_tag(CCATOM, 10, true));
        let root_only_adapter = SatisfiableTaskClassificationMessageAdapter::new(
            testing_concept,
            EFEXTRACTSUBSUMERSROOTNODE,
        );
        let subsumer_adapter = SatisfiableTaskClassificationMessageAdapter::new(
            testing_concept,
            EFEXTRACTSUBSUMERSOTHERNODES,
        );
        let possible_adapter = SatisfiableTaskClassificationMessageAdapter::new(
            testing_concept,
            EFEXTRACTPOSSIBLESUBSUMERSOTHERNODES,
        );

        assert!(
            !SatisfiableTaskClassificationMessageAnalyser::should_consider_other_nodes(
                &root_only_adapter,
            )
        );
        assert!(
            SatisfiableTaskClassificationMessageAnalyser::should_consider_other_nodes(
                &subsumer_adapter,
            )
        );
        assert!(
            SatisfiableTaskClassificationMessageAnalyser::should_consider_other_nodes(
                &possible_adapter,
            )
        );
        assert!(
            SatisfiableTaskClassificationMessageAnalyser::is_other_node_analysis_allowed(
                false, false,
            )
        );
        assert!(
            !SatisfiableTaskClassificationMessageAnalyser::is_other_node_analysis_allowed(
                true, false,
            )
        );
        assert!(
            !SatisfiableTaskClassificationMessageAnalyser::is_other_node_analysis_allowed(
                false, true,
            )
        );
    }

    #[test]
    fn classification_message_analyser_other_node_bfs_visits_allowed_successors_once() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut concepts = Arena::new();
        let testing_concept = concepts.push(concept_with_tag(CCATOM, 10, true));
        let skipped_first = concepts.push(concept_with_tag(CCATOM, 15, true));
        let first = concepts.push(concept_with_tag(CCATOM, 20, true));
        let skipped_second = concepts.push(concept_with_tag(CCATOM, 25, true));
        let second = concepts.push(concept_with_tag(CCATOM, 30, true));
        let skipped_third = concepts.push(concept_with_tag(CCATOM, 35, true));
        let third = concepts.push(concept_with_tag(CCATOM, 40, true));
        let adapter = SatisfiableTaskClassificationMessageAdapter::new(
            testing_concept,
            EFEXTRACTSUBSUMERSOTHERNODES | EFEXTRACTOTHERNODESMULTIPLEDEPENDENCY,
        );
        let snapshots = vec![
            ClassificationAnalyserOtherNodeSnapshot {
                individual_id: 1,
                is_nominal_individual_node: false,
                has_invalidate_blocker_flags: false,
                has_successor_nominal_connection: false,
                labels: vec![
                    ClassificationAnalyserConceptLabel::new(skipped_first, false, Some(1)),
                    ClassificationAnalyserConceptLabel::new(first, false, Some(1)),
                ],
                single_dependency_label_index: None,
                successor_individual_ids: vec![2, 3],
            },
            ClassificationAnalyserOtherNodeSnapshot {
                individual_id: 2,
                is_nominal_individual_node: false,
                has_invalidate_blocker_flags: false,
                has_successor_nominal_connection: false,
                labels: vec![
                    ClassificationAnalyserConceptLabel::new(skipped_second, false, Some(1)),
                    ClassificationAnalyserConceptLabel::new(second, false, Some(1)),
                ],
                single_dependency_label_index: None,
                successor_individual_ids: vec![3],
            },
            ClassificationAnalyserOtherNodeSnapshot {
                individual_id: 3,
                is_nominal_individual_node: false,
                has_invalidate_blocker_flags: false,
                has_successor_nominal_connection: false,
                labels: vec![
                    ClassificationAnalyserConceptLabel::new(skipped_third, false, Some(1)),
                    ClassificationAnalyserConceptLabel::new(third, false, Some(1)),
                ],
                single_dependency_label_index: None,
                successor_individual_ids: Vec::new(),
            },
        ];

        let visits = analyser.collect_other_node_analyse_visits(&adapter, 0, &[1, 2], &snapshots);

        assert_eq!(
            visits
                .iter()
                .map(|visit| (visit.individual_id, visit.label.concept))
                .collect::<Vec<_>>(),
            vec![(1, first), (2, second), (3, third)]
        );
    }

    #[test]
    fn classification_message_analyser_other_node_bfs_does_not_expand_skipped_nodes() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut concepts = Arena::new();
        let testing_concept = concepts.push(concept_with_tag(CCATOM, 10, true));
        let blocked_concept = concepts.push(concept_with_tag(CCATOM, 20, true));
        let hidden_successor = concepts.push(concept_with_tag(CCATOM, 30, true));
        let adapter = SatisfiableTaskClassificationMessageAdapter::new(
            testing_concept,
            EFEXTRACTSUBSUMERSOTHERNODES | EFEXTRACTOTHERNODESMULTIPLEDEPENDENCY,
        );
        let snapshots = vec![
            ClassificationAnalyserOtherNodeSnapshot {
                individual_id: 1,
                is_nominal_individual_node: false,
                has_invalidate_blocker_flags: true,
                has_successor_nominal_connection: false,
                labels: vec![ClassificationAnalyserConceptLabel::new(
                    blocked_concept,
                    false,
                    Some(1),
                )],
                single_dependency_label_index: None,
                successor_individual_ids: vec![2],
            },
            ClassificationAnalyserOtherNodeSnapshot {
                individual_id: 2,
                is_nominal_individual_node: false,
                has_invalidate_blocker_flags: false,
                has_successor_nominal_connection: false,
                labels: vec![ClassificationAnalyserConceptLabel::new(
                    hidden_successor,
                    false,
                    Some(1),
                )],
                single_dependency_label_index: None,
                successor_individual_ids: Vec::new(),
            },
        ];

        let visits = analyser.collect_other_node_analyse_visits(&adapter, 0, &[1], &snapshots);

        assert!(visits.is_empty());
    }

    #[test]
    fn classification_message_analyser_other_node_bfs_marks_single_dependency_descriptor() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut concepts = Arena::new();
        let testing_concept = concepts.push(concept_with_tag(CCATOM, 10, true));
        let first = concepts.push(concept_with_tag(CCATOM, 20, true));
        let single = concepts.push(concept_with_tag(CCATOM, 30, true));
        let third = concepts.push(concept_with_tag(CCATOM, 40, true));
        let adapter = SatisfiableTaskClassificationMessageAdapter::new(
            testing_concept,
            EFEXTRACTSUBSUMERSOTHERNODES
                | EFEXTRACTOTHERNODESMULTIPLEDEPENDENCY
                | EFEXTRACTOTHERNODESSINGLEDEPENDENCY,
        );
        let snapshots = vec![ClassificationAnalyserOtherNodeSnapshot {
            individual_id: 1,
            is_nominal_individual_node: false,
            has_invalidate_blocker_flags: false,
            has_successor_nominal_connection: false,
            labels: vec![
                ClassificationAnalyserConceptLabel::new(first, false, Some(1)),
                ClassificationAnalyserConceptLabel::new(single, false, Some(1)),
                ClassificationAnalyserConceptLabel::new(third, false, Some(1)),
            ],
            single_dependency_label_index: Some(1),
            successor_individual_ids: Vec::new(),
        }];

        let visits = analyser.collect_other_node_analyse_visits(&adapter, 0, &[1], &snapshots);

        assert_eq!(
            visits
                .iter()
                .map(|visit| (visit.label.concept, visit.is_single_dependency_descriptor))
                .collect::<Vec<_>>(),
            vec![(first, false), (single, true), (third, false)]
        );
    }

    #[test]
    fn classification_message_analyser_other_node_bfs_single_dependency_falls_back_when_absent() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut concepts = Arena::new();
        let testing_concept = concepts.push(concept_with_tag(CCATOM, 10, true));
        let first = concepts.push(concept_with_tag(CCATOM, 20, true));
        let adapter = SatisfiableTaskClassificationMessageAdapter::new(
            testing_concept,
            EFEXTRACTSUBSUMERSOTHERNODES | EFEXTRACTOTHERNODESSINGLEDEPENDENCY,
        );
        let snapshots = vec![ClassificationAnalyserOtherNodeSnapshot {
            individual_id: 1,
            is_nominal_individual_node: false,
            has_invalidate_blocker_flags: false,
            has_successor_nominal_connection: false,
            labels: vec![ClassificationAnalyserConceptLabel::new(
                first,
                false,
                Some(1),
            )],
            single_dependency_label_index: None,
            successor_individual_ids: Vec::new(),
        }];

        let visits = analyser.collect_other_node_analyse_visits(&adapter, 0, &[1], &snapshots);

        assert_eq!(visits.len(), 1);
        assert_eq!(visits[0].label.concept, first);
        assert!(!visits[0].is_single_dependency_descriptor);
    }

    #[test]
    fn classification_message_analyser_other_node_bfs_uses_single_dependency_without_multiple_extraction(
    ) {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut concepts = Arena::new();
        let testing_concept = concepts.push(concept_with_tag(CCATOM, 10, true));
        let first = concepts.push(concept_with_tag(CCATOM, 20, true));
        let single = concepts.push(concept_with_tag(CCATOM, 30, true));
        let adapter = SatisfiableTaskClassificationMessageAdapter::new(
            testing_concept,
            EFEXTRACTSUBSUMERSOTHERNODES | EFEXTRACTOTHERNODESSINGLEDEPENDENCY,
        );
        let snapshots = vec![ClassificationAnalyserOtherNodeSnapshot {
            individual_id: 1,
            is_nominal_individual_node: false,
            has_invalidate_blocker_flags: false,
            has_successor_nominal_connection: false,
            labels: vec![
                ClassificationAnalyserConceptLabel::new(first, false, Some(1)),
                ClassificationAnalyserConceptLabel::new(single, false, Some(1)),
            ],
            single_dependency_label_index: Some(1),
            successor_individual_ids: Vec::new(),
        }];

        let visits = analyser.collect_other_node_analyse_visits(&adapter, 0, &[1], &snapshots);

        assert_eq!(visits.len(), 1);
        assert_eq!(visits[0].label.concept, single);
        assert!(visits[0].is_single_dependency_descriptor);
    }

    #[test]
    fn classification_message_analyser_live_other_node_bfs_collects_successor_snapshots() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let ontology = OntologyArenas::new();
        let root = add_identified_node(&mut process_context, 0);
        let first = add_identified_node(&mut process_context, 1);
        let second = add_identified_node(&mut process_context, 2);
        let third = add_identified_node(&mut process_context, 3);
        let role = RoleId::new(5);
        add_role_link(&mut process_context, root, first, role, TrackPointId::NONE);
        add_role_link(&mut process_context, root, second, role, TrackPointId::NONE);
        add_role_link(&mut process_context, first, third, role, TrackPointId::NONE);

        let (root_successors, snapshots) =
            analyser.collect_live_other_node_snapshots_from_root(&process_context, &ontology, root);

        let mut sorted_root_successors = root_successors;
        sorted_root_successors.sort_unstable();
        assert_eq!(sorted_root_successors, vec![1, 2]);
        let mut sorted_snapshot_ids = snapshots
            .iter()
            .map(|snapshot| snapshot.individual_id)
            .collect::<Vec<_>>();
        sorted_snapshot_ids.sort_unstable();
        assert_eq!(sorted_snapshot_ids, vec![1, 2, 3]);
    }

    #[test]
    fn classification_message_analyser_live_other_node_bfs_does_not_expand_blocked_nodes() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let ontology = OntologyArenas::new();
        let root = add_identified_node(&mut process_context, 0);
        let blocked = add_identified_node(&mut process_context, 1);
        let hidden = add_identified_node(&mut process_context, 2);
        process_context
            .node_mut(blocked)
            .add_processing_restriction_flags(
                IndividualProcessNode::PRF_INVALIDATEBLOCKERFLAGSCOMPINATION,
            );
        let role = RoleId::new(5);
        add_role_link(
            &mut process_context,
            root,
            blocked,
            role,
            TrackPointId::NONE,
        );
        add_role_link(
            &mut process_context,
            blocked,
            hidden,
            role,
            TrackPointId::NONE,
        );

        let (root_successors, snapshots) =
            analyser.collect_live_other_node_snapshots_from_root(&process_context, &ontology, root);

        assert_eq!(root_successors, vec![1]);
        assert_eq!(snapshots.len(), 1);
        assert_eq!(snapshots[0].individual_id, 1);
        assert!(snapshots[0].has_invalidate_blocker_flags);
    }

    #[test]
    fn classification_message_analyser_extracts_other_node_snapshot_from_process_node() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let mut concepts = Arena::new();
        let first = concepts.push(concept_with_tag(CCATOM, 10, true));
        let second = concepts.push(concept_with_tag(CCATOM, 20, true));
        let role = RoleId::new(5);
        let mut dep_a = DependencyTrackPoint::new(DependencyId::NONE);
        dep_a.process_tag = 3;
        let track_a = process_context.alloc_track_point(dep_a);
        let mut dep_b = DependencyTrackPoint::new(DependencyId::NONE);
        dep_b.process_tag = 7;
        let track_b = process_context.alloc_track_point(dep_b);
        let node = add_identified_node(&mut process_context, 101);
        let succ_a = add_identified_node(&mut process_context, 201);
        let succ_b = add_identified_node(&mut process_context, 301);
        let label_set = process_context.alloc_label_set(ReapplyConceptLabelSet::new(0));
        process_context
            .node_mut(node)
            .set_reapply_concept_label_set(label_set);
        add_label_descriptor(
            &mut process_context,
            label_set,
            &concepts,
            first,
            false,
            track_a,
        );
        add_label_descriptor(
            &mut process_context,
            label_set,
            &concepts,
            second,
            true,
            track_b,
        );
        add_role_link(&mut process_context, node, succ_a, role, track_a);
        add_role_link(&mut process_context, node, succ_b, role, track_b);

        let snapshot = analyser
            .extract_other_node_snapshot_from_process_node(&process_context, node, Some(1))
            .expect("other-node snapshot");

        assert_eq!(snapshot.individual_id, 101);
        assert!(!snapshot.is_nominal_individual_node);
        assert!(!snapshot.has_invalidate_blocker_flags);
        assert!(!snapshot.has_successor_nominal_connection);
        assert_eq!(snapshot.single_dependency_label_index, Some(1));
        assert_eq!(snapshot.successor_individual_ids.len(), 2);
        assert!(snapshot.successor_individual_ids.contains(&201));
        assert!(snapshot.successor_individual_ids.contains(&301));
        assert_eq!(
            snapshot
                .labels
                .iter()
                .map(|label| (label.concept, label.negated, label.branching_tag))
                .collect::<Vec<_>>(),
            vec![(first, false, Some(3)), (second, true, Some(7))]
        );
    }

    #[test]
    fn classification_message_analyser_other_node_snapshot_preserves_node_flags() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let node = add_node(
            &mut process_context,
            IndividualProcessNode::PRF_INVALIDATEBLOCKERFLAGSCOMPINATION
                | IndividualProcessNode::PRF_SUCCESSORNOMINALCONNECTION,
            true,
        );
        process_context.node_mut(node).set_individual_node_id(77);

        let snapshot = analyser
            .extract_other_node_snapshot_from_process_node(&process_context, node, None)
            .expect("other-node snapshot");

        assert_eq!(snapshot.individual_id, 77);
        assert!(snapshot.is_nominal_individual_node);
        assert!(snapshot.has_invalidate_blocker_flags);
        assert!(snapshot.has_successor_nominal_connection);
        assert!(snapshot.labels.is_empty());
        assert!(snapshot.successor_individual_ids.is_empty());
    }

    #[test]
    fn classification_message_analyser_selects_single_ancestor_dependency_descriptor() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let mut ontology = OntologyArenas::new();
        let skipped_tag_one = ontology.alloc_concept(concept_with_tag(CCATOM, 1, true));
        let selected_concept = ontology.alloc_concept(concept_with_tag(CCATOM, 20, true));
        let current = add_node(&mut process_context, 0, false);
        let ancestor = add_node(&mut process_context, 0, false);
        process_context
            .node_mut(current)
            .set_individual_ancestor_depth(3);
        process_context
            .node_mut(ancestor)
            .set_individual_ancestor_depth(1);
        let label_set = process_context.alloc_label_set(ReapplyConceptLabelSet::new(0));
        process_context
            .node_mut(current)
            .set_reapply_concept_label_set(label_set);
        let skipped_descriptor = add_ontology_label_descriptor(
            &mut process_context,
            label_set,
            &ontology,
            skipped_tag_one,
            false,
            TrackPointId::NONE,
        );
        let ancestor_track = add_dependency_track_point(
            &mut process_context,
            DepKind::And,
            ancestor,
            TrackPointId::NONE,
        );
        let selected_descriptor = add_ontology_label_descriptor(
            &mut process_context,
            label_set,
            &ontology,
            selected_concept,
            false,
            ancestor_track,
        );
        process_context
            .con_desc_mut(skipped_descriptor)
            .set_next(selected_descriptor);
        process_context
            .con_desc_mut(selected_descriptor)
            .set_next(ConDescId::NONE);
        process_context.label_set_mut(label_set).concept_des_linker = skipped_descriptor;

        assert!(analyser.has_dependency_to_ancestor(&process_context, current, ancestor_track));
        assert_eq!(
            analyser.individual_process_node_concept_with_single_ancestor_dependency(
                &process_context,
                &ontology,
                current,
            ),
            Some(selected_descriptor)
        );
        assert_eq!(
            analyser.single_ancestor_dependency_label_index_from_process_node(
                &process_context,
                &ontology,
                current,
            ),
            Some(1)
        );
    }

    #[test]
    fn classification_message_analyser_resolves_merged_concept_ancestor_dependency_snapshot() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let mut ontology = OntologyArenas::new();
        let concept = ontology.alloc_concept(concept_with_tag(CCATOM, 10, true));
        let current = add_identified_node(&mut process_context, 909);
        let ancestor = add_node(&mut process_context, 0, false);
        process_context
            .node_mut(current)
            .set_individual_ancestor_depth(4);
        process_context
            .node_mut(ancestor)
            .set_individual_ancestor_depth(2);
        let label_set = process_context.alloc_label_set(ReapplyConceptLabelSet::new(0));
        process_context
            .node_mut(current)
            .set_reapply_concept_label_set(label_set);
        let ancestor_track = add_dependency_track_point(
            &mut process_context,
            DepKind::Some,
            ancestor,
            TrackPointId::NONE,
        );
        let merged_track = add_dependency_track_point(
            &mut process_context,
            DepKind::MergedConcept,
            NodeId::NONE,
            ancestor_track,
        );
        let selected_descriptor = add_ontology_label_descriptor(
            &mut process_context,
            label_set,
            &ontology,
            concept,
            true,
            merged_track,
        );

        assert!(analyser.has_dependency_to_ancestor(&process_context, current, merged_track));
        assert_eq!(
            analyser.individual_process_node_concept_with_single_ancestor_dependency(
                &process_context,
                &ontology,
                current,
            ),
            Some(selected_descriptor)
        );

        let snapshot = analyser
            .extract_other_node_snapshot_from_process_node_resolving_single_dependency(
                &process_context,
                &ontology,
                current,
            )
            .expect("other-node snapshot");
        assert_eq!(snapshot.individual_id, 909);
        assert_eq!(snapshot.single_dependency_label_index, Some(0));
        assert_eq!(
            snapshot
                .labels
                .iter()
                .map(|label| (label.concept, label.negated))
                .collect::<Vec<_>>(),
            vec![(concept, true)]
        );
    }

    #[test]
    fn classification_message_analyser_single_ancestor_dependency_rejects_cpp_cases() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let mut ontology = OntologyArenas::new();
        let first = ontology.alloc_concept(concept_with_tag(CCATOM, 10, true));
        let second = ontology.alloc_concept(concept_with_tag(CCATOM, 20, true));
        let current = add_node(&mut process_context, 0, false);
        let ancestor = add_node(&mut process_context, 0, false);
        process_context
            .node_mut(current)
            .set_individual_ancestor_depth(3);
        process_context
            .node_mut(ancestor)
            .set_individual_ancestor_depth(1);
        let label_set = process_context.alloc_label_set(ReapplyConceptLabelSet::new(0));
        process_context
            .node_mut(current)
            .set_reapply_concept_label_set(label_set);
        let ancestor_track = add_dependency_track_point(
            &mut process_context,
            DepKind::And,
            ancestor,
            TrackPointId::NONE,
        );
        let first_descriptor = add_ontology_label_descriptor(
            &mut process_context,
            label_set,
            &ontology,
            first,
            false,
            ancestor_track,
        );
        let second_descriptor = add_ontology_label_descriptor(
            &mut process_context,
            label_set,
            &ontology,
            second,
            false,
            ancestor_track,
        );
        process_context
            .con_desc_mut(first_descriptor)
            .set_next(second_descriptor);
        process_context
            .con_desc_mut(second_descriptor)
            .set_next(ConDescId::NONE);
        process_context.label_set_mut(label_set).concept_des_linker = first_descriptor;
        assert_eq!(
            analyser.individual_process_node_concept_with_single_ancestor_dependency(
                &process_context,
                &ontology,
                current,
            ),
            None
        );

        let null_dep_node = add_node(&mut process_context, 0, false);
        let null_dep_label_set = process_context.alloc_label_set(ReapplyConceptLabelSet::new(0));
        process_context
            .node_mut(null_dep_node)
            .set_reapply_concept_label_set(null_dep_label_set);
        add_ontology_label_descriptor(
            &mut process_context,
            null_dep_label_set,
            &ontology,
            first,
            false,
            TrackPointId::NONE,
        );
        assert_eq!(
            analyser.individual_process_node_concept_with_single_ancestor_dependency(
                &process_context,
                &ontology,
                null_dep_node,
            ),
            None
        );

        let successor_connection_node = add_node(
            &mut process_context,
            IndividualProcessNode::PRF_SUCCESSORNOMINALCONNECTION,
            false,
        );
        let successor_label_set = process_context.alloc_label_set(ReapplyConceptLabelSet::new(0));
        process_context
            .node_mut(successor_connection_node)
            .set_reapply_concept_label_set(successor_label_set);
        add_ontology_label_descriptor(
            &mut process_context,
            successor_label_set,
            &ontology,
            first,
            false,
            ancestor_track,
        );
        assert_eq!(
            analyser.individual_process_node_concept_with_single_ancestor_dependency(
                &process_context,
                &ontology,
                successor_connection_node,
            ),
            None
        );
    }

    #[test]
    fn classification_message_analyser_other_node_visits_create_class_and_possible_messages() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut concepts = Arena::new();
        let testing_concept = concepts.push(concept_with_tag(CCATOM, 10, true));
        let analyse_concept = concepts.push(concept_with_tag(CCATOM, 20, true));
        let same_branch_subsumer = concepts.push(concept_with_tag(CCATOM, 30, true));
        let adapter = SatisfiableTaskClassificationMessageAdapter::new(
            testing_concept,
            EFEXTRACTSUBSUMERSOTHERNODES
                | EFEXTRACTPOSSIBLESUBSUMERSOTHERNODES
                | EFEXTRACTOTHERNODESSINGLEDEPENDENCY,
        );
        let snapshots = vec![ClassificationAnalyserOtherNodeSnapshot {
            individual_id: 1,
            is_nominal_individual_node: false,
            has_invalidate_blocker_flags: false,
            has_successor_nominal_connection: false,
            labels: vec![
                ClassificationAnalyserConceptLabel::new(analyse_concept, false, Some(7)),
                ClassificationAnalyserConceptLabel::new(same_branch_subsumer, false, Some(7)),
            ],
            single_dependency_label_index: Some(0),
            successor_individual_ids: Vec::new(),
        }];
        let visits = vec![ClassificationAnalyserOtherNodeVisit {
            individual_id: 1,
            label: snapshots[0].labels[0],
            is_single_dependency_descriptor: true,
        }];
        let mut required = std::collections::HashSet::new();
        required.insert(analyse_concept);
        let mut analysed = std::collections::HashSet::new();

        let (class_linker, poss_linker) = analyser
            .create_other_node_classification_message_linkers(
                &adapter,
                testing_concept,
                &visits,
                &snapshots,
                &required,
                &mut analysed,
                &std::collections::HashMap::new(),
                &std::collections::HashMap::new(),
                &concepts,
            );

        let class_linker = class_linker.expect("class message linker");
        let mut class_messages = class_linker.iter();
        let Some(ClassificationMessageDataPayload::ClassSubsumption(class_message)) =
            class_messages.next()
        else {
            panic!("expected class-subsumption message");
        };
        assert_eq!(class_message.get_subsumed_concept(), analyse_concept);
        assert_eq!(
            class_message.get_class_subsumer_list(),
            Some([same_branch_subsumer].as_slice())
        );
        assert!(class_messages.next().is_none());

        let poss_linker = poss_linker.expect("possible-subsumption message linker");
        assert_eq!(
            poss_linker.message_types(),
            vec![ClassificationMessageDataType::TellClassInitializePossibleSubsumption]
        );
        assert!(analysed.contains(&analyse_concept));
    }

    #[test]
    fn classification_message_analyser_other_node_visit_messages_prepend_and_deduplicate() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut concepts = Arena::new();
        let testing_concept = concepts.push(concept_with_tag(CCATOM, 10, true));
        let first_analyse = concepts.push(concept_with_tag(CCATOM, 20, true));
        let first_subsumer = concepts.push(concept_with_tag(CCATOM, 30, true));
        let second_analyse = concepts.push(concept_with_tag(CCATOM, 40, true));
        let second_subsumer = concepts.push(concept_with_tag(CCATOM, 50, true));
        let adapter = SatisfiableTaskClassificationMessageAdapter::new(
            testing_concept,
            EFEXTRACTSUBSUMERSOTHERNODES | EFEXTRACTOTHERNODESSINGLEDEPENDENCY,
        );
        let snapshots = vec![
            ClassificationAnalyserOtherNodeSnapshot {
                individual_id: 1,
                is_nominal_individual_node: false,
                has_invalidate_blocker_flags: false,
                has_successor_nominal_connection: false,
                labels: vec![
                    ClassificationAnalyserConceptLabel::new(first_analyse, false, Some(7)),
                    ClassificationAnalyserConceptLabel::new(first_subsumer, false, Some(7)),
                ],
                single_dependency_label_index: Some(0),
                successor_individual_ids: Vec::new(),
            },
            ClassificationAnalyserOtherNodeSnapshot {
                individual_id: 2,
                is_nominal_individual_node: false,
                has_invalidate_blocker_flags: false,
                has_successor_nominal_connection: false,
                labels: vec![
                    ClassificationAnalyserConceptLabel::new(second_analyse, false, Some(9)),
                    ClassificationAnalyserConceptLabel::new(second_subsumer, false, Some(9)),
                ],
                single_dependency_label_index: Some(0),
                successor_individual_ids: Vec::new(),
            },
        ];
        let visits = vec![
            ClassificationAnalyserOtherNodeVisit {
                individual_id: 1,
                label: snapshots[0].labels[0],
                is_single_dependency_descriptor: true,
            },
            ClassificationAnalyserOtherNodeVisit {
                individual_id: 2,
                label: snapshots[1].labels[0],
                is_single_dependency_descriptor: true,
            },
            ClassificationAnalyserOtherNodeVisit {
                individual_id: 1,
                label: snapshots[0].labels[0],
                is_single_dependency_descriptor: true,
            },
        ];
        let mut required = std::collections::HashSet::new();
        required.insert(first_analyse);
        required.insert(second_analyse);
        let mut analysed = std::collections::HashSet::new();

        let (class_linker, poss_linker) = analyser
            .create_other_node_classification_message_linkers(
                &adapter,
                testing_concept,
                &visits,
                &snapshots,
                &required,
                &mut analysed,
                &std::collections::HashMap::new(),
                &std::collections::HashMap::new(),
                &concepts,
            );

        assert!(poss_linker.is_none());
        let class_linker = class_linker.expect("class message linker");
        let subsumed_concepts = class_linker
            .iter()
            .map(|payload| match payload {
                ClassificationMessageDataPayload::ClassSubsumption(message) => {
                    message.get_subsumed_concept()
                }
                _ => ConceptId::NONE,
            })
            .collect::<Vec<_>>();
        assert_eq!(subsumed_concepts, vec![second_analyse, first_analyse]);
        assert_eq!(analysed.len(), 2);
    }

    #[test]
    fn classification_message_analyser_creates_possible_subsumption_init_message() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut concepts = Arena::new();
        let testing_concept = concepts.push(concept_with_tag(CCATOM, 10, true));
        let named_candidate = concepts.push(concept_with_tag(CCATOM, 20, true));
        let negated_candidate = concepts.push(concept_with_tag(CCATOM, 30, true));
        let eq_candidate = concepts.push(concept_with_tag(CCEQCAND, 40, false));
        let eq_non_candidate = concepts.push(concept_with_tag(CCEQ, 50, true));
        let adapter = SatisfiableTaskClassificationMessageAdapter::new(
            testing_concept,
            EFEXTRACTPOSSIBLESUBSUMERSROOTNODE,
        );

        let payload = analyser
            .create_possible_class_subsumption_message(
                &adapter,
                testing_concept,
                &[
                    ClassificationAnalyserConceptLabel::new(named_candidate, false, Some(3)),
                    ClassificationAnalyserConceptLabel::new(negated_candidate, true, Some(3)),
                    ClassificationAnalyserConceptLabel::new_eq_candidate(
                        eq_candidate,
                        false,
                        Some(3),
                        true,
                    ),
                ],
                &ClassificationAnalyserPossibleSubsumptionState::uninitialized(),
                &[eq_non_candidate],
                &concepts,
            )
            .expect("possible init message");

        let ClassificationMessageDataPayload::InitializePossibleClassSubsumption(message) = payload
        else {
            panic!("expected initialize possible-subsumption payload");
        };
        let poss_list = message
            .get_class_possible_subsumer_list()
            .expect("possible list");
        assert_eq!(poss_list.len(), 2);
        assert_eq!(
            poss_list[0].get_possible_subsumer_concept(),
            named_candidate
        );
        assert_eq!(poss_list[1].get_possible_subsumer_concept(), eq_candidate);
        assert!(message.has_eq_concepts_non_candidate_poss_subsumers());
        assert_eq!(
            message.get_class_eq_concept_non_candidate_possible_subsumer_list(),
            Some([eq_non_candidate].as_slice())
        );
    }

    #[test]
    fn classification_message_template_preserves_order_and_testing_exclusion() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut concepts = Arena::new();
        let testing_concept = concepts.push(concept_with_tag(CCATOM, 20, true));
        let lower_candidate = concepts.push(concept_with_tag(CCATOM, 10, true));
        let eq_candidate = concepts.push(concept_with_tag(CCEQCAND, 30, false));
        let missing_candidate = concepts.push(concept_with_tag(CCATOM, 40, true));
        let labels = vec![
            ClassificationAnalyserConceptLabel::new(eq_candidate, false, Some(1)),
            ClassificationAnalyserConceptLabel::new(testing_concept, false, Some(1)),
            ClassificationAnalyserConceptLabel::new(lower_candidate, false, Some(1)),
            ClassificationAnalyserConceptLabel::new_eq_candidate(
                eq_candidate,
                false,
                Some(1),
                true,
            ),
        ];
        let adapter = SatisfiableTaskClassificationMessageAdapter::new(
            testing_concept,
            EFEXTRACTPOSSIBLESUBSUMERSROOTNODE,
        );
        let state = ClassificationAnalyserPossibleSubsumptionState::uninitialized();
        let ordinary = analyser
            .create_possible_class_subsumption_message(
                &adapter,
                testing_concept,
                &labels,
                &state,
                &[],
                &concepts,
            )
            .expect("ordinary message");
        let template = SatisfiableTaskClassificationMessageAnalyser::
            possible_subsumer_message_template(&labels, &concepts);
        let cached = analyser
            .create_possible_class_subsumption_message_with_equivalent_non_candidates(
                &adapter,
                testing_concept,
                &labels,
                &state,
                false,
                &[],
                Some(&template),
                None,
                &concepts,
            )
            .expect("cached message");

        let concepts_in = |payload: ClassificationMessageDataPayload| {
            let ClassificationMessageDataPayload::InitializePossibleClassSubsumption(message) =
                payload
            else {
                panic!("expected initialization message")
            };
            message
                .get_class_possible_subsumer_list()
                .unwrap_or(&[])
                .iter()
                .map(|candidate| candidate.get_possible_subsumer_concept())
                .collect::<Vec<_>>()
        };
        assert_eq!(concepts_in(cached), concepts_in(ordinary));

        let state = ClassificationAnalyserPossibleSubsumptionState::initialized(vec![
            missing_candidate,
        ]);
        let ordinary = analyser
            .create_possible_class_subsumption_message(
                &adapter,
                testing_concept,
                &labels,
                &state,
                &[],
                &concepts,
            )
            .expect("ordinary update");
        let label_tags = labels
            .iter()
            .map(|label| {
                SatisfiableTaskClassificationMessageAnalyser::concept_tag(label.concept, &concepts)
            })
            .collect();
        let cached = analyser
            .create_possible_class_subsumption_message_with_equivalent_non_candidates(
                &adapter,
                testing_concept,
                &labels,
                &state,
                false,
                &[],
                Some(&template),
                Some(&label_tags),
                &concepts,
            )
            .expect("cached update");
        assert!(matches!(
            ordinary,
            ClassificationMessageDataPayload::UpdatePossibleClassSubsumption(_)
        ));
        assert!(matches!(
            cached,
            ClassificationMessageDataPayload::UpdatePossibleClassSubsumption(_)
        ));
    }

    #[test]
    fn classification_message_analyser_live_eq_non_candidate_message_preserves_empty_set_flag() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let (node, label_set) = add_completion_label_set_node(&mut process_context);
        let mut ontology = OntologyArenas::new();
        let mut concepts = Arena::new();
        let roles = Arena::<Role>::new();
        let mut concept_process_datas = Arena::<ConceptProcessData>::new();
        let mut concept_reference_linking_datas =
            Arena::<ConceptSaturationReferenceLinkingData>::new();
        let mut saturation_reference_linkings = Arena::<SaturationConceptReferenceLinking>::new();
        let testing_concept = concepts.push(concept_with_tag(CCATOM, 10, true));
        let operand = concepts.push(concept_with_tag(CCATOM, 20, true));
        let mut filtered_equivalence = concept_with_tag(CCEQ, 30, true);
        filtered_equivalence.add_operand_linker(operand, false);
        let filtered_equivalence = concepts.push(filtered_equivalence);
        let (sat_node, _) = add_saturation_label_set_node(&mut process_context);
        let sat_ref = add_saturation_reference(&mut saturation_reference_linkings, sat_node);
        let mut ref_data = ConceptSaturationReferenceLinkingData::new();
        ref_data.set_saturation_reference_linking_data(sat_ref, true);
        attach_concept_reference_data(
            &mut concepts,
            operand,
            &mut concept_process_datas,
            &mut concept_reference_linking_datas,
            ref_data,
        );
        add_label_descriptor(
            &mut process_context,
            label_set,
            &concepts,
            operand,
            true,
            TrackPointId::NONE,
        );
        ontology.insert_equivalent_concept_non_candidate(filtered_equivalence);
        let adapter = SatisfiableTaskClassificationMessageAdapter::new(
            testing_concept,
            EFEXTRACTPOSSIBLESUBSUMERSROOTNODE,
        );

        let payload = analyser
            .create_possible_class_subsumption_message_with_live_equivalent_non_candidates(
                &adapter,
                testing_concept,
                &[],
                &ClassificationAnalyserPossibleSubsumptionState::uninitialized(),
                node,
                &ontology,
                &concepts,
                &roles,
                &concept_process_datas,
                &concept_reference_linking_datas,
                &saturation_reference_linkings,
                &mut process_context,
                None,
            )
            .expect("possible init message");

        let ClassificationMessageDataPayload::InitializePossibleClassSubsumption(message) = payload
        else {
            panic!("expected initialize possible-subsumption payload");
        };
        assert!(message.has_eq_concepts_non_candidate_poss_subsumers());
        assert!(message
            .get_class_eq_concept_non_candidate_possible_subsumer_list()
            .is_none());
    }

    #[test]
    fn classification_message_analyser_creates_possible_subsumption_update_only_for_missing_non_eq()
    {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut concepts = Arena::new();
        let testing_concept = concepts.push(concept_with_tag(CCATOM, 10, true));
        let retained_candidate = concepts.push(concept_with_tag(CCATOM, 20, true));
        let missing_candidate = concepts.push(concept_with_tag(CCATOM, 30, true));
        let missing_eq_candidate = concepts.push(concept_with_tag(CCEQ, 40, true));
        let adapter = SatisfiableTaskClassificationMessageAdapter::new(
            testing_concept,
            EFEXTRACTPOSSIBLESUBSUMERSROOTNODE,
        );
        let state = ClassificationAnalyserPossibleSubsumptionState::initialized(vec![
            retained_candidate,
            missing_candidate,
            missing_eq_candidate,
        ]);

        let payload = analyser
            .create_possible_class_subsumption_message(
                &adapter,
                testing_concept,
                &[ClassificationAnalyserConceptLabel::new(
                    retained_candidate,
                    false,
                    Some(3),
                )],
                &state,
                &[],
                &concepts,
            )
            .expect("possible update message");
        assert!(matches!(
            payload,
            ClassificationMessageDataPayload::UpdatePossibleClassSubsumption(_)
        ));

        let eq_only_state =
            ClassificationAnalyserPossibleSubsumptionState::initialized(vec![missing_eq_candidate]);
        assert!(analyser
            .create_possible_class_subsumption_message(
                &adapter,
                testing_concept,
                &[],
                &eq_only_state,
                &[],
                &concepts,
            )
            .is_none());
    }

    #[test]
    fn classification_message_analyser_prunes_reused_possible_subsumption_init_list() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut concepts = Arena::new();
        let retained_low = concepts.push(concept_with_tag(CCATOM, 10, true));
        let missing_middle = concepts.push(concept_with_tag(CCATOM, 20, true));
        let retained_high = concepts.push(concept_with_tag(CCATOM, 30, true));
        let missing_tail = concepts.push(concept_with_tag(CCATOM, 40, true));
        let mut possible_subsumers = vec![
            ClassificationInitializePossibleClassSubsumptionData::new(retained_low),
            ClassificationInitializePossibleClassSubsumptionData::new(missing_middle),
            ClassificationInitializePossibleClassSubsumptionData::new(retained_high),
            ClassificationInitializePossibleClassSubsumptionData::new(missing_tail),
        ];

        assert!(analyser.prune_reused_possible_subsumption_init_list(
            &[
                ClassificationAnalyserConceptLabel::new(retained_low, false, Some(1)),
                ClassificationAnalyserConceptLabel::new(retained_high, false, Some(1)),
            ],
            &mut possible_subsumers,
            &concepts,
        ));

        assert!(possible_subsumers[0].is_possible_subsumer_valid());
        assert!(!possible_subsumers[1].is_possible_subsumer_valid());
        assert!(possible_subsumers[2].is_possible_subsumer_valid());
        assert!(!possible_subsumers[3].is_possible_subsumer_valid());
    }

    #[test]
    fn classification_message_analyser_reused_possible_subsumption_prune_is_noop_when_tags_match() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut concepts = Arena::new();
        let first = concepts.push(concept_with_tag(CCATOM, 10, true));
        let second = concepts.push(concept_with_tag(CCATOM, 20, true));
        let mut possible_subsumers = vec![
            ClassificationInitializePossibleClassSubsumptionData::new(first),
            ClassificationInitializePossibleClassSubsumptionData::new(second),
        ];

        assert!(!analyser.prune_reused_possible_subsumption_init_list(
            &[
                ClassificationAnalyserConceptLabel::new(first, true, Some(1)),
                ClassificationAnalyserConceptLabel::new(second, false, Some(1)),
            ],
            &mut possible_subsumers,
            &concepts,
        ));

        assert!(possible_subsumers
            .iter()
            .all(|data| data.is_possible_subsumer_valid()));
    }

    #[test]
    fn classification_message_analyser_pseudo_model_producer_applies_depth_cap() {
        let analyser = SatisfiableTaskClassificationMessageAnalyser;
        let mut process_context = ProcessContext::new();
        let mut concepts = Arena::new();
        let mut roles = Arena::new();
        let role_r = roles.push(role_with_tag(10, false));
        let mut deterministic_tp = DependencyTrackPoint::new(DependencyId::NONE);
        deterministic_tp.process_tag = 1;
        let deterministic_tp = process_context.alloc_track_point(deterministic_tp);

        let mut nodes = Vec::new();
        for idx in 0..5 {
            let node = add_identified_node(&mut process_context, idx + 1);
            let concept = concepts.push(concept_with_tag(CCATOM, 100 + idx, true));
            let label_set = process_context.alloc_label_set(ReapplyConceptLabelSet::new(0));
            process_context
                .node_mut(node)
                .set_reapply_concept_label_set(label_set);
            add_label_descriptor(
                &mut process_context,
                label_set,
                &concepts,
                concept,
                false,
                deterministic_tp,
            );
            nodes.push((node, concept));
        }
        for idx in 0..4 {
            add_role_link(
                &mut process_context,
                nodes[idx].0,
                nodes[idx + 1].0,
                role_r,
                deterministic_tp,
            );
        }

        let adapter = SatisfiableTaskClassificationMessageAdapter::new(
            ConceptId::new(1),
            EFEXTRACTIDENTIFIERPSEUDOMODEL,
        );
        let message = analyser
            .create_pseudo_model_identifier_message_from_base_node(
                &adapter,
                &process_context,
                nodes[0].0,
                false,
                3,
                &concepts,
                &roles,
                0,
            )
            .expect("pseudo-model message");

        let hash = message.get_pseudo_model_hash();
        assert_eq!(hash.get_count(), 5);
        for model_id in 0..4 {
            let model = hash.get_pseudo_model_data(model_id).expect("model");
            assert!(model.has_valid_concept_map());
            assert!(model.has_valid_role_map());
        }
        let depth_capped_model = hash.get_pseudo_model_data(4).expect("depth capped model");
        assert!(depth_capped_model.has_valid_concept_map());
        assert!(!depth_capped_model.has_valid_role_map());
        assert!(depth_capped_model
            .get_pseudo_model_concept_map()
            .expect("depth concept map")
            .get(nodes[4].1)
            .expect("depth concept")
            .is_deterministic());
        assert!(depth_capped_model.get_pseudo_model_role_map().is_none());
    }
}
