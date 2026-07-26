//! `completion::u36` — Generic helpers / accessors / label tests family, batch
//! (port unit #36 of 36 — the LAST completion unit).
//!
//! Faithful port of the 19 methods the manifest (`01-completion-methods.md`,
//! "Unit 36") groups under the individual-node localisation accessors + the
//! concept-adding helpers + the concept-descriptor pool of Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.cpp`.
//! cpp source line ranges (1-based) are noted on each item.
//!
//! Methods (cpp order):
//!   * `getUpToDateIndividual(cint64 indiID,…)`                  [22506–22583]
//!   * `getPropagationSteeringController`                        [25707–25723]
//!   * `getLocalizedIndividual(cint64 indiID,…)`                 [26412–26414]
//!   * `getLocalizedIndividual(CIndividualProcessNode*,bool,…)`  [26416–26444]
//!   * `getSuccessorIndividual`                                  [26446–26461]
//!   * `getLocalizedSuccessorIndividual`                         [26464–26477]
//!   * `getAncestorIndividual`                                   [26480–26488]
//!   * `addConceptToIndividual`                                  [26725–26753]
//!   * `addConceptToIndividualReturnConceptDescriptor`           [26757–26782]
//!   * `setIndividualNodeAncestorConnectionModified`            [26786–26788]
//!   * `setIndividualNodeConceptLabelSetModified`               [26790–26796]
//!   * `isIndividualNodeConceptLabelSetModified`                [26800–26802]
//!   * `createConceptDescriptor`                                 [26809–26817]
//!   * `releaseConceptDescriptor`                               [26820–26824]
//!   * `addConceptsToIndividual(CSortedNegLinker<CConcept*>*,…)` [26829–26869]
//!   * `insertConceptsToIndividualConceptSet`                   [26925–27021]
//!   * `addConceptsToIndividual(CConceptAssertionLinker*,…)`     [27026–27064]
//!   * `addConceptsToIndividual(CXNegLinker<CConcept*>*,…)`      [27068–27106]
//!   * `addConceptsToIndividual(CXSortedNegLinker<CConcept*>*,…)`[27110–27148]
//!
//! KONCLUDE-PORT-NOTE[ownership]: each method is a member of
//! `CCalculationTableauCompletionTaskHandleAlgorithm`, so it becomes `&mut self`
//! plus the threaded per-thread context `calc_alg_context: &mut
//! CalculationAlgorithmContextBase`. C++ `CIndividualProcessNode*&` in/out
//! pointer-references become `&mut NodeId`; a plain `CIndividualProcessNode*`
//! value parameter becomes `NodeId`; `CConcept*` → `ConceptId` (resolved against
//! `calc_alg_context.ontology_arenas()`); `CIndividualLinkEdge*` → `EdgeId`;
//! `CConceptDescriptor*` → `ConDescId`; `CDependencyTrackPoint*` → `TrackPointId`.
//! The per-test arenas are reached through the context as
//! `calc_alg_context.process_context()` / `_mut()`, the databox as
//! `calc_alg_context.processing_data_box{,_mut}()`.
//!
//! KONCLUDE-PORT-NOTE[overload]: C++ overloads the same name on parameter type;
//! Rust cannot, so the port disambiguates by an explicit suffix while keeping the
//! C++ name as the anchor in each doc-comment:
//!   * `getUpToDateIndividual(cint64)`  → `get_up_to_date_individual_by_id`
//!     (the `CIndividualProcessNode*` overload, cpp 22485, is a sibling of another
//!     unit: `get_up_to_date_individual(node, ctx)`);
//!   * `getLocalizedIndividual(cint64)` → `get_localized_individual_by_id`;
//!   * `getLocalizedIndividual(node,bool)` → `get_localized_individual`;
//!   * the four `addConceptsToIndividual` linker overloads collapse to the same
//!     port representation `&[NegLink<ConceptId>]` (every Konclude concept-linker
//!     chain — `CSortedNegLinker`/`CConceptAssertionLinker`/`CXNegLinker`/
//!     `CXSortedNegLinker` — exposes `getData()`/`isNegated()`/`getNext()`, so
//!     they flatten to one slice, the u06/u14 convention) and are distinguished by
//!     the `…_from_*_linker` suffix. The primary `CSortedNegLinker` overload keeps
//!     the bare name `add_concepts_to_individual` (the name the existing u08/u34
//!     call sites use).
//!
//! Deferral landscape. Two leaf subsystems gate the localisation accessors:
//!   * the LOCALISATION tag protocol — `CIndividualProcessNode::isLocalizationTagUpToDate`
//!     / `CIndividualLinkEdge::isLocalizationTagUpToDate` /
//!     `…->getOppositeIndividual(indi)` / `…->getOppositeIndividualID(indi)` and the
//!     `CProcessTagger::getCurrentLocalizationTag` reader are NOT yet ported (the
//!     edge accessors + the tagger stub have no methods); and
//!   * the databox `getIndividualProcessNodeVector()` / `getIndividualVector()`
//!     trackers + their `getData()/setLocalData()` are process-layer stubs (no
//!     arena lookup yet).
//! So `getSuccessorIndividual`, `getLocalizedSuccessorIndividual`,
//! `getLocalizedIndividual(node,bool)` and `getUpToDateIndividual(cint64)` are kept
//! `// PORT-PENDING` with the faithful structural transcription + the C++ default
//! return; `getAncestorIndividual` and `getLocalizedIndividual(cint64)` ARE live
//! (pure delegation onto the in-unit siblings).
//!
//! The concept-adding helpers ARE substrate-portable in their decisive control
//! flow (the create-descriptor / insert / not-contained / release loop), calling
//! the in-unit siblings (`create_concept_descriptor`, `release_concept_descriptor`,
//! `insert_concepts_to_individual_concept_set`, `set_individual_node_concept_label_set_modified`)
//! and the cross-unit siblings (`add_blocking_core_concept`,
//! `add_concept_preprocessed_to_processing_queue`, `apply_reapply_queue_concepts`)
//! via `self.x(...)`; only the genuine leaves stay deferred: `STATINC` (W3-DEFER[macro]),
//! the `CConceptDescriptor::initConceptDescriptor` derived init (W2 descriptor
//! method — set the public fields directly), and the
//! `throw CCalculationClashProcessingException` channel
//! (W3-DEFER[exceptions], not yet established at this layer). Logic is documented,
//! never silently dropped.

#![allow(dead_code)]
#![allow(unused_variables)]

use std::collections::HashSet;

use super::super::model::individual::{ReverseRoleAssertion, RoleAssertion};
use super::super::model::substrate::{Cint64, Id, NegLink, INVALID};
use super::super::model::{ConceptId, IndividualId, RoleId};
use super::super::process::descriptor::ClashDescriptor;
use super::super::process::marker_hash::MarkerIndividualNodeHash;
use super::super::process::node::{IndividualProcessNode, IndividualType};
use super::super::process::reapply_sat::CondensedReapplyQueueIterator;
use super::super::process::satellites::ReapplyConceptLabelSet;
use super::super::process::{ConDescId, EdgeId, LabelSetId, NodeId, TrackPointId};
use super::context::CalculationAlgorithmContextBase;

/// KONCLUDE-PORT-NOTE[api]: `CAnsweringPropagationSteeringController*` is a Task /
/// answerer-message subsystem class (W6) — until it lands the steering controller
/// is an opaque `Cint64` handle (`INVALID` == `nullptr`).
type PropagationSteeringController = Cint64;

impl super::algorithm::CompletionTaskHandleAlgorithm {
    pub(crate) fn native_nominal_tag_for_node(
        &self,
        node: NodeId,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> Option<Cint64> {
        if node.is_none() || node.index() >= calc_alg_context.process_context().node_count() {
            return None;
        }
        let individual = calc_alg_context
            .process_context()
            .node(node)
            .nominal_individual();
        if individual.is_none()
            || individual.index() >= calc_alg_context.ontology_arenas().individual_count() as usize
        {
            return None;
        }
        Some(
            calc_alg_context
                .ontology_arenas()
                .individual(individual)
                .get_individual_id(),
        )
    }

    // =======================================================================
    // Typed `mBackendCacheHandler` accessors for the native-ABox association.
    //
    // The generic representative-memory cache (`CBackendRepresentativeMemory*`)
    // is not ported; the bridge installs one immutable
    // `NativeNominalBackendReplay` per ontology individual instead. These four
    // methods are the exact typed counterparts of the four backend-cache-handler
    // queries that the neighbour-expansion family issues, so u20/u24/u27 can run
    // their faithful Konclude control flow against real data. The association
    // HANDLE is the nominal individual tag (Konclude's
    // `CBackendRepresentativeMemoryCacheIndividualAssociationData*`).
    // =======================================================================

    /// Typed `mBackendCacheHandler->getIndividualAssociationData(indiID, ctx)`:
    /// the nominal tag of `node` iff a replay association is installed for it.
    pub(crate) fn native_association_tag(
        &self,
        node: NodeId,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> Option<Cint64> {
        let tag = self.native_nominal_tag_for_node(node, calc_alg_context)?;
        self.native_nominal_backend_replay
            .get(&tag)
            .filter(|replay| replay.association_present)
            .map(|_| tag)
    }

    /// Typed `mBackendCacheHandler->hasConceptInAssociatedFullConceptSetLabel(
    /// assocData, FULL_CONCEPT_SET_LABEL, concept, negation, deterministic, ctx)`.
    ///
    /// The trailing C++ flag selects the label PARTITION, not "at least
    /// deterministic": `canExpandDirectlyInfluencedNeighbourWithPropagation`
    /// queries `true` and then, for a non-deterministic expansion, `false`, which
    /// is only meaningful if the two searches address the deterministic and the
    /// non-deterministic cache values respectively. The typed cache value carries
    /// that bit explicitly, so the test is exact membership of the triple.
    pub(crate) fn native_has_concept_in_full_concept_set_label(
        &self,
        assoc_tag: Cint64,
        concept: ConceptId,
        negated: bool,
        deterministic: bool,
    ) -> bool {
        self.native_nominal_backend_replay
            .get(&assoc_tag)
            .is_some_and(|replay| {
                replay
                    .cached_concept_values
                    .binary_search_by_key(
                        &(concept.raw, negated, deterministic),
                        |(cached_concept, cached_negated, cached_deterministic)| {
                            (cached_concept.raw, *cached_negated, *cached_deterministic)
                        },
                    )
                    .is_ok()
            })
    }

    /// Typed `mBackendCacheHandler->hasRoleInAssociatedCompinationRoleSetLabel(
    /// assocData, {DETERMINISTIC,NONDETERMINISTIC}_COMBINED_NEIGHBOUR_INSTANTIATED_ROLE_SET_LABEL,
    /// role, inversed)` (spelled `…CombinedNeigbourRoleSetLabel` at the sibling
    /// call site — the same predicate).
    ///
    /// The two combined labels are the determinism partition of the per-neighbour
    /// role sets, so the typed test scans the cached neighbour-role values for a
    /// matching `(role, inversed, deterministic)` triple.
    pub(crate) fn native_has_role_in_combined_neighbour_role_set_label(
        &self,
        assoc_tag: Cint64,
        role: RoleId,
        deterministic: bool,
        inversed: bool,
    ) -> bool {
        self.native_nominal_backend_replay
            .get(&assoc_tag)
            .is_some_and(|replay| {
                replay.cached_neighbour_roles.iter().any(
                    |&(_, cached_role, cached_inversed, cached_deterministic)| {
                        cached_role == role
                            && cached_inversed == inversed
                            && cached_deterministic == deterministic
                    },
                )
            })
    }

    /// Typed `mBackendCacheHandler->visitNeighbourArrayIdsForRole` followed by
    /// `visitNeighbourIndividualIdsForNeighbourArrayIdFromCursor`.
    ///
    /// The typed association stores one neighbour-role-set label per neighbour, so
    /// a role's neighbour array IS its neighbour list and no cursor is needed; the
    /// per-neighbour `isNeighbourPossiblyInfluenced()` bit on the localized
    /// backend-sync data still supplies Konclude's re-visit suppression.
    /// Non-inversed values only: an inversed cached value is the neighbour's
    /// outgoing edge, expanded from the neighbour's own association.
    pub(crate) fn native_neighbour_ids_for_role(
        &self,
        assoc_tag: Cint64,
        role: RoleId,
    ) -> Vec<(Cint64, bool)> {
        let Some(replay) = self.native_nominal_backend_replay.get(&assoc_tag) else {
            return Vec::new();
        };
        // One entry per neighbour. A neighbour that carries the role both
        // deterministically and non-deterministically is reported deterministic:
        // that is the value the replay may install on the base dependency.
        let mut neighbours: Vec<(Cint64, bool)> = Vec::new();
        for &(neighbour, cached_role, inversed, deterministic) in &replay.cached_neighbour_roles {
            if cached_role != role || inversed {
                continue;
            }
            match neighbours
                .iter_mut()
                .find(|(existing, _)| *existing == neighbour)
            {
                Some(entry) => entry.1 |= deterministic,
                None => neighbours.push((neighbour, deterministic)),
            }
        }
        neighbours
    }

    /// Typed `mBackendCacheHandler->getIndividualAssociationData(neighbourIndiId, …)`
    /// as an opaque handle: the individual tag itself when an association is
    /// installed, `INVALID` (the C++ `nullptr`) otherwise.
    pub(crate) fn native_association_handle_for_individual(&self, individual_tag: Cint64) -> Cint64 {
        if self
            .native_nominal_backend_replay
            .get(&individual_tag)
            .is_some_and(|replay| replay.association_present)
        {
            individual_tag
        } else {
            INVALID
        }
    }

    /// Typed `assocData->getNeighbourRoleSetHash()->getNeighbourRoleSetLabel(
    /// neighbourNodeId)`: the `(role, deterministic)` values of one neighbour's
    /// role-set label, non-inversed only.
    pub(crate) fn native_neighbour_role_set_label_roles(
        &self,
        assoc_tag: Cint64,
        neighbour_tag: Cint64,
    ) -> Vec<(RoleId, bool)> {
        let Some(replay) = self.native_nominal_backend_replay.get(&assoc_tag) else {
            return Vec::new();
        };
        replay
            .cached_neighbour_roles
            .iter()
            .filter(|(cached_neighbour, _, inversed, _)| {
                *cached_neighbour == neighbour_tag && !*inversed
            })
            .map(|(_, role, _, deterministic)| (*role, *deterministic))
            .collect()
    }

    /// Is `role(indiNode, neighbourTag)` one of `indi_node`'s ASSERTED ABox role
    /// assertions?
    ///
    /// The typed representative association marks a neighbour-role value
    /// NON-deterministic whenever either endpoint was merged non-deterministically
    /// (`bridge::native_completion_role_metadata`'s
    /// `edge_deterministic = source_merge_deterministic && target_merge_deterministic`).
    /// That says nothing about the edge itself: an ABox role assertion holds in
    /// EVERY model, so its cache marking cannot make it branch-dependent. The raw
    /// replay fallback (`materialize_native_role_assertion_vectors`) installs
    /// exactly this edge from exactly this chain on the task's base dependency, so
    /// the cache-backed route may install it there too.
    ///
    /// Used to keep the per-neighbour decline of the selective expansion (u27) from
    /// degenerating into a per-NODE cache loss.
    pub(crate) fn native_asserted_role_edge(
        &self,
        indi_node: NodeId,
        role: RoleId,
        neighbour_tag: Cint64,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> bool {
        if indi_node.is_none()
            || indi_node.index() >= calc_alg_context.process_context().node_count()
            || role.is_none()
        {
            return false;
        }
        let asserted_on_node = calc_alg_context
            .process_context()
            .node(indi_node)
            .assertion_role_assertions()
            .iter()
            .any(|assertion| {
                assertion.role == role
                    && assertion.individual.is_some()
                    && assertion.individual.index()
                        < calc_alg_context.ontology_arenas().individual_count() as usize
                    && calc_alg_context
                        .ontology_arenas()
                        .individual(assertion.individual)
                        .get_individual_id()
                        == neighbour_tag
            });
        if asserted_on_node {
            return true;
        }
        // A lazily materialized node copies the same chain, but the bridge's typed
        // replay journal is the authoritative record when
        // `direct_native_role_assertions` owns the edges.
        self.native_nominal_tag_for_node(indi_node, calc_alg_context)
            .and_then(|tag| self.native_nominal_backend_replay.get(&tag))
            .is_some_and(|replay| replay.role_assertions.contains(&(role, neighbour_tag)))
    }

    /// May a NON-deterministic cached neighbour-role value be installed on the
    /// task's base dependency?
    ///
    /// Only when the edge is an asserted ABox role assertion — see
    /// `native_asserted_role_edge`. A merely DERIVED non-deterministic value
    /// is not entailed and the raw replay fallback would not install it either
    /// (`materialize_native_role_assertion_vectors` replays the assertion chains
    /// only), so skipping it installs exactly the same edge set while keeping the
    /// node's association block.
    pub(crate) fn native_cached_role_value_installable(
        &self,
        indi_node: NodeId,
        role: RoleId,
        neighbour_tag: Cint64,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> bool {
        self.conf_native_selective_neighbour_per_value_decline
            && self.native_asserted_role_edge(indi_node, role, neighbour_tag, calc_alg_context)
    }

    /// `assocData->isCompletelyPropagated()` on the typed association.
    pub(crate) fn native_association_completely_propagated(&self, assoc_tag: Cint64) -> bool {
        self.native_nominal_backend_replay
            .get(&assoc_tag)
            .is_some_and(|replay| replay.completely_propagated)
    }

    /// The `nonDeterministicConsequencesMissingExpansion` test of
    /// `initializeNeighbourExpansionWithPropagation` (cpp 25620–25626): the
    /// neighbour's FULL_CONCEPT_SET label must carry a cardinality extension
    /// (`CARDINALITY_HASH`) or a non-deterministic element.
    pub(crate) fn native_label_has_nondeterministic_consequences(
        &self,
        assoc_tag: Cint64,
    ) -> bool {
        self.native_nominal_backend_replay
            .get(&assoc_tag)
            .is_some_and(|replay| {
                !replay.cached_at_most_cardinalities.is_empty()
                    || !replay.cached_existential_max_cardinalities.is_empty()
                    || replay
                        .cached_concept_values
                        .iter()
                        .any(|(_, _, deterministic)| !*deterministic)
            })
    }

    fn native_cached_neighbour_role_matches(
        &self,
        node: NodeId,
        neighbour_tag: Cint64,
        role: RoleId,
        inversed: bool,
        deterministic: bool,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> bool {
        let Some(tag) = self.native_nominal_tag_for_node(node, calc_alg_context) else {
            return false;
        };
        self.native_nominal_backend_replay
            .get(&tag)
            .filter(|replay| replay.neighbour_expansion_blocking_candidate)
            .is_some_and(|replay| {
                replay
                    .cached_neighbour_roles
                    .binary_search_by_key(
                        &(neighbour_tag, role.raw, inversed, deterministic),
                        |(cached_neighbour, cached_role, cached_inversed, cached_deterministic)| {
                            (
                                *cached_neighbour,
                                cached_role.raw,
                                *cached_inversed,
                                *cached_deterministic,
                            )
                        },
                    )
                    .is_ok()
            })
    }

    /// Materialize the value-backed forward and reverse assertion chains that
    /// `getUpToDateIndividual` copied from the ontology individual. The two
    /// initialized bits are set before recursive named-neighbour loading so a
    /// cyclic ABox cannot recursively replay the same assertion.
    pub(crate) fn materialize_native_role_assertion_vectors(
        &mut self,
        node: NodeId,
        dependency_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        if node.is_none() || node.index() >= calc_alg_context.process_context().node_count() {
            return false;
        }
        let (
            role_assertions_initialized,
            reverse_role_assertions_initialized,
            role_assertions,
            reverse_role_assertions,
            own_tag,
        ): (
            bool,
            bool,
            Vec<RoleAssertion>,
            Vec<ReverseRoleAssertion>,
            Cint64,
        ) = {
            let process_context = calc_alg_context.process_context();
            let node_ref = process_context.node(node);
            let Some(own_tag) = self.native_nominal_tag_for_node(node, calc_alg_context) else {
                return false;
            };
            (
                node_ref.has_role_assertions_initialized(),
                node_ref.has_reverse_role_assertions_initialized(),
                node_ref.assertion_role_assertions().to_vec(),
                node_ref.reverse_assertion_role_assertions().to_vec(),
                own_tag,
            )
        };
        if role_assertions_initialized && reverse_role_assertions_initialized {
            return true;
        }
        calc_alg_context
            .process_context_mut()
            .node_mut(node)
            .set_role_assertions_initialized(true)
            .set_reverse_role_assertions_initialized(true);

        if !role_assertions_initialized {
            for assertion in role_assertions {
                if assertion.individual.is_none()
                    || assertion.individual.index()
                        >= calc_alg_context.ontology_arenas().individual_count() as usize
                {
                    return false;
                }
                let target_tag = calc_alg_context
                    .ontology_arenas()
                    .individual(assertion.individual)
                    .get_individual_id();
                if !self.install_native_role_assertion_edge(
                    node,
                    assertion.role,
                    target_tag,
                    dependency_track_point,
                    calc_alg_context,
                ) {
                    return false;
                }
                if calc_alg_context.has_pending_signal() {
                    return true;
                }
            }
        }
        if !reverse_role_assertions_initialized {
            for assertion in reverse_role_assertions {
                if assertion.individual.is_none()
                    || assertion.individual.index()
                        >= calc_alg_context.ontology_arenas().individual_count() as usize
                {
                    return false;
                }
                let source_tag = calc_alg_context
                    .ontology_arenas()
                    .individual(assertion.individual)
                    .get_individual_id();
                let source = self.get_up_to_date_individual_by_id(-source_tag, calc_alg_context);
                if source.is_none()
                    || !self.install_native_role_assertion_edge(
                        source,
                        assertion.role,
                        own_tag,
                        dependency_track_point,
                        calc_alg_context,
                    )
                {
                    return false;
                }
                if calc_alg_context.has_pending_signal() {
                    return true;
                }
            }
        }
        true
    }

    /// Schedule Konclude's backend-synchronisation retest without consuming
    /// either raw assertion linker. The retest decides whether the change is
    /// neighbour/cardinality critical and expands only the affected cached
    /// neighbours. Eagerly clearing these flags here would turn one local
    /// concept change into recursive materialisation of the whole ABox.
    pub(crate) fn invalidate_native_nominal_backend_blocking(
        &mut self,
        node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let Some(tag) = self.native_nominal_tag_for_node(node, calc_alg_context) else {
            return false;
        };
        if !self.native_nominal_backend_replay.contains_key(&tag) {
            return false;
        }
        let native_blocking_flags = IndividualProcessNode::PRF_SYNCHRONIZEDBACKEND
            | IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDSUCCESSOREXPANSIONBLOCKED
            | IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDNEIGHBOUREXPANSIONBLOCKED
            | IndividualProcessNode::PRF_SYNCHRONIZEDBACKENNEIGHBOURDPARTIALEXPANSION
            | IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDINDIRECTNOMINALEXPANSIONBLOCKED;
        if !calc_alg_context
            .process_context()
            .node(node)
            .has_partial_processing_restriction_flags(native_blocking_flags)
        {
            return false;
        }
        if !calc_alg_context
            .process_context()
            .node(node)
            .has_partial_processing_restriction_flags(
                IndividualProcessNode::PRF_RETESTBACKENDSYNCHRONIZATIONDUEDIRECTMODIFIED,
            )
        {
            calc_alg_context
                .process_context_mut()
                .node_mut(node)
                .add_processing_restriction_flags(
                    IndividualProcessNode::PRF_RETESTBACKENDSYNCHRONIZATIONDUEDIRECTMODIFIED,
                );
        }
        self.add_individual_to_backend_synchronisation_retest_queue(node, calc_alg_context);
        true
    }

    /// Konclude's FULL_CONCEPT_SET synchronization check for the typed native
    /// representative replay. Every current descriptor except the positive own
    /// nominal must occur in the cached label with the same determinism bit.
    fn native_replay_concepts_synchronized(
        &mut self,
        node: NodeId,
        replay: &super::algorithm::NativeNominalBackendReplay,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let label = calc_alg_context
            .process_context()
            .node(node)
            .reapply_con_label_set;
        if label.is_none() {
            return false;
        }
        let mut descriptor = calc_alg_context
            .process_context()
            .label_set(label)
            .get_adding_sorted_concept_description_linker();
        let mut walked = 0usize;
        while descriptor.is_some() {
            if descriptor.index() >= calc_alg_context.process_context().con_desc_count()
                || walked > calc_alg_context.process_context().con_desc_count()
            {
                return false;
            }
            let (concept, negated, dependency_track_point, next) = {
                let descriptor_ref = calc_alg_context.process_context().con_desc(descriptor);
                (
                    descriptor_ref.get_concept(),
                    descriptor_ref.is_negated(),
                    descriptor_ref.get_dependency_track_point(),
                    descriptor_ref.get_next_concept_descriptor(),
                )
            };
            if concept != replay.own_nominal_concept || negated {
                let deterministic =
                    !self.has_nondeterministic_dependency(dependency_track_point, calc_alg_context);
                if replay
                    .cached_concept_values
                    .binary_search_by_key(&(concept.raw, negated, deterministic), |value| {
                        (value.0.raw, value.1, value.2)
                    })
                    .is_err()
                {
                    return false;
                }
            }
            descriptor = next;
            walked += 1;
        }
        true
    }

    pub(crate) fn native_cardinality_critical_roles(
        &self,
        node: NodeId,
        replay: &super::algorithm::NativeNominalBackendReplay,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> Vec<RoleId> {
        let successor_blocked = calc_alg_context
            .process_context()
            .node(node)
            .has_partial_processing_restriction_flags(
                IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDSUCCESSOREXPANSIONBLOCKED,
            );
        let mut roles = Vec::new();
        for &(role, minimum_restricting_cardinality) in
            &replay.cached_at_most_cardinalities
        {
            let current = calc_alg_context
                .process_context()
                .node(node)
                .get_role_successor_count(role);
            let existential = if successor_blocked {
                replay
                    .cached_existential_max_cardinalities
                    .binary_search_by_key(&role.raw, |(cached_role, _)| cached_role.raw)
                    .ok()
                    .map(|index| replay.cached_existential_max_cardinalities[index].1)
                    .unwrap_or(0)
            } else {
                0
            };
            let cached_neighbours = replay
                .cached_neighbour_roles
                .iter()
                .filter(|(_, cached_role, inversed, _)| {
                    *cached_role == role && !*inversed
                })
                .map(|(neighbour, _, _, _)| *neighbour)
                .collect::<HashSet<_>>()
                .len() as Cint64;
            if current
                .saturating_add(existential)
                .saturating_add(cached_neighbours)
                > minimum_restricting_cardinality
            {
                roles.push(role);
            }
        }
        roles.sort_unstable_by_key(|role| role.raw);
        roles.dedup();
        roles
    }

    /// Typed native counterpart of Konclude's
    /// `detectIndividualNodeBackendCacheSynchronized` (cpp 4231–4288) followed by
    /// the assertion-linker call site that consumes it (cpp 8919–8952).
    ///
    /// The C++ shape is reproduced exactly:
    ///
    /// ```text
    /// detectIndividualNodeBackendCacheSynchronized(indiNode, ctx);
    /// if (!hasPartialFlags(PRFSYNCHRONIZEDBACKENDNEIGHBOUREXPANSIONBLOCKED)) {
    ///   if (mConfAllowBackendNeighbourExpansionBlocking)
    ///     addFlags(PRFSYNCHRONIZEDBACKENNEIGHBOURDPARTIALEXPANSION);
    ///   if (!backendSyncData
    ///       || !expandDirectlyInfluencedIndividualNeighbourNodesFromBackendCache(indiNode, ctx)) {
    ///     clearAssertionRoles(); clearReverseAssertionRoles();
    ///     for every assertion linker: addRoleAssertion(...);   // raw replay
    ///   }
    /// }
    /// ```
    ///
    /// so the cache-backed SELECTIVE expansion always precedes the raw
    /// bidirectional assertion replay, and the replay runs only when the
    /// selective expansion declines. Returns false only for an impossible typed
    /// state (the caller then stops the task); an ordinary "nothing to expand" is
    /// `true`.
    pub(crate) fn process_native_nominal_backend_retest(
        &mut self,
        node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        if node.is_none() || node.index() >= calc_alg_context.process_context().node_count() {
            return true;
        }
        // `detectIndividualNodeBackendCacheSynchronized`'s outer guard: only a node
        // that holds one of the five backend-synchronization flags has anything
        // cache-backed left to decide.
        let native_blocking_flags = IndividualProcessNode::PRF_SYNCHRONIZEDBACKEND
            | IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDSUCCESSOREXPANSIONBLOCKED
            | IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDNEIGHBOUREXPANSIONBLOCKED
            | IndividualProcessNode::PRF_SYNCHRONIZEDBACKENNEIGHBOURDPARTIALEXPANSION
            | IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDINDIRECTNOMINALEXPANSIONBLOCKED;
        if !calc_alg_context
            .process_context()
            .node(node)
            .has_partial_processing_restriction_flags(native_blocking_flags)
        {
            return true;
        }
        let Some(tag) = self.native_association_tag(node, calc_alg_context) else {
            return true;
        };
        let Some(replay) = self.native_nominal_backend_replay.get(&tag).cloned() else {
            return true;
        };

        if calc_alg_context
            .process_context()
            .node(node)
            .has_partial_processing_restriction_flags(
                IndividualProcessNode::PRF_RETESTBACKENDSYNCHRONIZATIONDUEDIRECTMODIFIED,
            )
        {
            calc_alg_context
                .process_context_mut()
                .node_mut(node)
                .clear_processing_restriction_flags(
                    IndividualProcessNode::PRF_RETESTBACKENDSYNCHRONIZATIONDUEDIRECTMODIFIED,
                );

            // if (hasPartialFlags(PRFSYNCHRONIZEDBACKEND)
            //     && !testIndividualNodeBackendCacheConceptsSynchronization(indiNode, ctx)) {
            //   clear PRFSYNCHRONIZEDBACKEND; clear PRFSYNCHRONIZEDBACKENDSUCCESSOREXPANSIONBLOCKED; }
            if calc_alg_context
                .process_context()
                .node(node)
                .has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_SYNCHRONIZEDBACKEND,
                )
                && !self.native_replay_concepts_synchronized(node, &replay, calc_alg_context)
            {
                calc_alg_context
                    .process_context_mut()
                    .node_mut(node)
                    .clear_processing_restriction_flags(
                        IndividualProcessNode::PRF_SYNCHRONIZEDBACKEND
                            | IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDSUCCESSOREXPANSIONBLOCKED,
                    );
            }

            // W6-DEFER[api]: `testIndividualNodeBackendCacheSameMergedBlockingCritical`
            // reads the deterministic same-individual label. The trace records that
            // label empty on all 198 roots of the studied ontology and 0 roots
            // deterministically merged, and the bridge rejects source
            // `SameIndividual`, so the typed association never carries a
            // deterministic merge for this predicate to release on.

            // if (hasPartialFlags(NEIGHBOUREXPANSIONBLOCKED)
            //     && testIndividualNodeBackendCacheNeighbourExpansionBlockingCritical(indiNode, ctx))
            //   clear NEIGHBOUREXPANSIONBLOCKED;
            if calc_alg_context
                .process_context()
                .node(node)
                .has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDNEIGHBOUREXPANSIONBLOCKED,
                )
                && self.test_individual_node_backend_cache_neighbour_expansion_blocking_critical(
                    node,
                    calc_alg_context,
                )
            {
                calc_alg_context
                    .process_context_mut()
                    .node_mut(node)
                    .clear_processing_restriction_flags(
                        IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDNEIGHBOUREXPANSIONBLOCKED,
                    );
            }

            // if (hasPartialFlags(NEIGHBOUREXPANSIONBLOCKED | SUCCESSOREXPANSIONBLOCKED)
            //     && testIndividualNodeBackendCacheExpansionBlockingCriticalCardinality(indiNode, ctx)) {
            //   clear SUCCESSOREXPANSIONBLOCKED; clear NEIGHBOUREXPANSIONBLOCKED; }
            if calc_alg_context
                .process_context()
                .node(node)
                .has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDNEIGHBOUREXPANSIONBLOCKED
                        | IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDSUCCESSOREXPANSIONBLOCKED,
                )
                && self
                    .test_individual_node_backend_cache_expansion_blocking_critical_cardinality(
                        node,
                        calc_alg_context,
                    )
            {
                calc_alg_context
                    .process_context_mut()
                    .node_mut(node)
                    .clear_processing_restriction_flags(
                        IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDSUCCESSOREXPANSIONBLOCKED
                            | IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDNEIGHBOUREXPANSIONBLOCKED,
                    );
            }

            // W6-DEFER[api]: the INDIRECTNOMINALEXPANSIONBLOCKED release needs
            // `testIndividualNodeBackendCacheNominalIndirectConnectionBlockingCritical`
            // (u17, PORT-PENDING). Keeping the bit set is the conservative
            // direction — it never skips work — and
            // `install_native_role_assertion_edge` clears it explicitly on any
            // target it modifies outside the cached neighbour view.
        }

        // cpp 8919/8740: the raw assertion linkers are consumed only while the
        // neighbour-expansion block is released, and never once a full expansion
        // has already been performed.
        if calc_alg_context
            .process_context()
            .node(node)
            .has_partial_processing_restriction_flags(
                IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDNEIGHBOUREXPANSIONBLOCKED
                    | IndividualProcessNode::PRF_SYNCHRONIZEDBACKENNEIGHBOURDFULLEXPANSION,
            )
        {
            return true;
        }
        if self.conf_allow_backend_neighbour_expansion_blocking {
            calc_alg_context
                .process_context_mut()
                .node_mut(node)
                .add_processing_restriction_flags(
                    IndividualProcessNode::PRF_SYNCHRONIZEDBACKENNEIGHBOURDPARTIALEXPANSION,
                );
        }
        if self.expand_directly_influenced_individual_neighbour_nodes_from_backend_cache(
            node,
            calc_alg_context,
        ) {
            return true;
        }
        if calc_alg_context.has_pending_signal() {
            return true;
        }

        // Exact C++ fallback (cpp 8940–8952): a declined selective expansion
        // consumes both raw assertion chains. Once every named edge has been
        // materialized the cached association can no longer justify any expansion
        // block, so the remaining synchronization bits are dropped and the node is
        // marked fully expanded.
        calc_alg_context
            .process_context_mut()
            .node_mut(node)
            .clear_processing_restriction_flags(native_blocking_flags);
        calc_alg_context
            .process_context_mut()
            .node_mut(node)
            .add_processing_restriction_flags(
                IndividualProcessNode::PRF_SYNCHRONIZEDBACKENNEIGHBOURDFULLEXPANSION
                    | IndividualProcessNode::PRF_INVALIDBLOCKINGORCACHING,
            );
        let dependency_track_point = {
            let point = calc_alg_context
                .process_context()
                .node(node)
                .dependency_track_point();
            if point.is_some() {
                point
            } else {
                calc_alg_context.get_or_create_base_dependency_track_point()
            }
        };
        self.materialize_native_role_assertion_vectors(
            node,
            dependency_track_point,
            calc_alg_context,
        )
    }

    /// Copy one positive native ABox role assertion exactly as Konclude's
    /// `addRoleAssertion`: materialize/correct the named target, create the
    /// deterministic role-assertion dependency, then install all indirect
    /// super-role and inverse links with domain/range and reapply processing.
    pub fn install_native_role_assertion_edge(
        &mut self,
        source: NodeId,
        role: RoleId,
        target_tag: Cint64,
        prev_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        if source.is_none() || role.is_none() || target_tag < 0 {
            return false;
        }
        let original_target = self.get_up_to_date_individual_by_id(-target_tag, calc_alg_context);
        if original_target.is_none() {
            return false;
        }
        let (mut target, nominal_merge_track_point) = if calc_alg_context
            .process_context()
            .node(original_target)
            .has_merged_into_individual_node_id()
        {
            let first_target_id = calc_alg_context
                .process_context()
                .node(original_target)
                .merged_into_individual_node_id();
            let first_target =
                self.get_up_to_date_individual_by_id(first_target_id, calc_alg_context);
            if first_target.is_none()
                || calc_alg_context
                    .process_context()
                    .node(first_target)
                    .has_merged_into_individual_node_id()
            {
                // Konclude retrieves the combined b→…→representative
                // dependency from the final node's IndividualMergingHash.
                // Rust phase-6 merging-hash propagation is not ported yet, so
                // a chain longer than one hop cannot be justified exactly.
                // Decline the bridge route instead of omitting a branch cause
                // while dependency-directed backtracking is active.
                return false;
            }
            (
                first_target,
                calc_alg_context
                    .process_context()
                    .node(original_target)
                    .merged_dependency_track_point(),
            )
        } else {
            (original_target, TrackPointId::NONE)
        };
        target = self.get_localized_forced_backend_initialized_nominal_individual_node(
            target,
            calc_alg_context,
        );
        let mut source_ref = source;
        let mut target_ref = target;
        if self.has_individuals_link(
            &mut source_ref,
            &mut target_ref,
            role,
            true,
            calc_alg_context,
        ) {
            return true;
        }
        let source_tag = self.native_nominal_tag_for_node(source, calc_alg_context);
        let edge_deterministic = !self
            .has_nondeterministic_dependency(prev_dep_track_point, calc_alg_context)
            && (nominal_merge_track_point.is_none()
                || !self
                    .has_nondeterministic_dependency(nominal_merge_track_point, calc_alg_context));
        let cached_target_edge = source_tag.is_some_and(|source_tag| {
            self.native_cached_neighbour_role_matches(
                target,
                source_tag,
                role,
                true,
                edge_deterministic,
                calc_alg_context,
            )
        });
        // A newly installed incoming assertion changes the target's
        // neighbour, inverse-role, cardinality, and indirect-nominal view.
        // Generic backend retesting cannot validate the bridge-local replay
        // record and otherwise leaves the indirect-nominal blocking bit set.
        // Fail closed before any reapply work observes the modified target.
        let native_blocking_flags = IndividualProcessNode::PRF_SYNCHRONIZEDBACKEND
            | IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDSUCCESSOREXPANSIONBLOCKED
            | IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDINDIRECTNOMINALEXPANSIONBLOCKED;
        if !cached_target_edge
            && calc_alg_context
                .process_context()
                .node(target)
                .has_partial_processing_restriction_flags(native_blocking_flags)
        {
            calc_alg_context
                .process_context_mut()
                .node_mut(target)
                .clear_processing_restriction_flags(native_blocking_flags);
        }
        let source_individual = calc_alg_context
            .process_context()
            .node(source)
            .nominal_individual();
        if source_individual.is_none() {
            return false;
        }
        let mut assertion_track_point = TrackPointId::NONE;
        self.create_role_assertion_dependency(
            &mut assertion_track_point,
            source,
            prev_dep_track_point,
            nominal_merge_track_point,
            role,
            source_individual,
            calc_alg_context,
        );
        if assertion_track_point.is_none() {
            assertion_track_point = prev_dep_track_point;
        }
        let mut super_roles = calc_alg_context
            .ontology_arenas()
            .role(role)
            .get_indirect_super_role_list()
            .to_vec();
        if !super_roles
            .iter()
            .any(|link| link.target == role && !link.negated)
        {
            super_roles.push(NegLink {
                target: role,
                negated: false,
            });
        }
        let link = self.create_new_individuals_links_reapplyed(
            source,
            target,
            &super_roles,
            role,
            assertion_track_point,
            true,
            calc_alg_context,
        );
        if link.is_some() {
            if !cached_target_edge {
                self.propagate_individual_node_modified(&mut target, calc_alg_context);
                self.add_individual_to_processing_queue(target, calc_alg_context);
            }
            true
        } else {
            self.has_individuals_link(
                &mut source_ref,
                &mut target_ref,
                role,
                true,
                calc_alg_context,
            )
        }
    }

    // NODE-RESOLUTION SUPERSESSION: the node-resolution family below
    // (`get_up_to_date_individual_by_id` / `get_localized_individual{,_by_id}` /
    // `get_successor_individual` / `get_localized_successor_individual` /
    // `get_ancestor_individual`) was lifted onto `CalculationAlgorithmContextBase`
    // in `process/node_resolution.rs` (real node-vector + tagger). These
    // algorithm-method stubs are kept for diff-fidelity but are superseded by
    // `ctx.*` — the un-defer wave calls `calc_alg_context.get_up_to_date_individual(…)`
    // etc. directly.
    // =======================================================================
    // getUpToDateIndividual(cint64 indiID, …)  (cpp 22506–22583).
    // =======================================================================

    /// Port of `getUpToDateIndividual(cint64 indiID, CCalculationAlgorithmContextBase*)`.
    /// cpp 22506–22583. KONCLUDE-PORT-NOTE[overload]: the `cint64` overload — see
    /// the bare-`NodeId` sibling `get_up_to_date_individual` (cpp 22485, other unit).
    pub fn get_up_to_date_individual_by_id(
        &mut self,
        indi_id: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        // W3-DEFER[macro]: STATINC(INDINODEUPDATELOADCOUNT, calcAlgContext);
        //
        // PORT-PENDING: faithful transcription of cpp 22506–22583. Outline:
        //
        //   indiProcNodeVec = calcAlgContext->getProcessingDataBox()->getIndividualProcessNodeVector();
        //   upToDateIndi = indiProcNodeVec->getData(indiID);
        //   if (!upToDateIndi) {
        //     indiVec = calcAlgContext->getProcessingDataBox()->getIndividualVector(false);
        //     if (indiVec && indiID <= 0) {
        //       individual = indiVec->getData(-indiID);
        //       if (!individual) individual = createNewTemporaryNominalIndividual(-indiID, ctx);   // sibling
        //       if (individual) {
        //         trackIndividualReferredDependence(indiID, ctx);                                   // dep sibling
        //         STATINC(INDINODELOCALIZEDLOADCOUNT, ctx);
        //         localicedIndi = ctx.used_process_context_mut().alloc_node(IndividualProcessNode::new(procCtx));
        //         depTrackPoint = ctx.getBaseDependencyNode()->getContinueDependencyTrackPoint();
        //         localicedIndi.init_dependency_tracker(depTrackPoint);
        //         localicedIndi.set_nominal_individual(individual);
        //         localicedIndi.set_individual_type(NOMINALINDIVIDUALTYPE);
        //         localicedIndi.set_individual_node_id(indiID);
        //         indiProcNodeVec->setLocalData(localicedIndi.individual_node_id(), localicedIndi);
        //         localicedIndi.set_assertion_role_linker(individual->getAssertionRoleLinker());
        //         localicedIndi.set_reverse_assertion_role_linker(individual->getReverseAssertionRoleLinker());
        //         localicedIndi.set_assertion_data_linker(individual->getAssertionDataLinker());
        //         localicedIndi.set_role_assertion_creation_id(databox.next_role_assertion_creation_id());
        //         localicedIndi.set_nominal_individual_triples_assertions(true);
        //         univConnNomValueConcept = databox->getOntology()->getTBox()->getUniversalConnectionNominalValueConcept();
        //         if (univConnNomValueConcept) self.add_concept_to_individual(univConnNomValueConcept,false,localicedIndi,depTrackPoint,true,true,ctx);
        //         nominalConcept = individual->getIndividualNominalConcept();
        //         if (nominalConcept) self.add_concept_to_individual(nominalConcept,false,localicedIndi,depTrackPoint,true,true,ctx);
        //         if (mOptConsistenceNodeMarking) localicedIndi.add_processing_restriction_flags(PRF_CONSNODEPREPARATIONINDINODE);
        //         if (!mOptIncrementalCompatibleExpansion) {
        //           expansionBlocked = false;
        //           if (loadIndividualNodeDataFromBackendCache(localicedIndi, ctx)) {              // backend siblings
        //             localicedIndi.set_nominal_individual_representative_backend_data_loaded(true);
        //             initializeIndividualNodeWithBackendCache(localicedIndi, ctx);
        //             expansionBlocked = tryEstablishExpansionBlockingWithBackendCacheSynchronisation(localicedIndi, ctx);
        //           }
        //           if (!expansionBlocked) self.add_individual_to_processing_queue(localicedIndi, ctx);
        //         } else {
        //           localicedIndi.set_assertion_concept_linker(individual->getAssertionConceptLinker());
        //           localicedIndi.set_incremental_expansion_id(databox.incremental_expansion_id());
        //           localicedIndi.add_processing_restriction_flags(PRF_INCREMENTALEXPANDING);
        //           expData = localicedIndi.incremental_expansion_data(true);
        //           expData->setExpansionID(databox.next_incremental_individual_expansion_id(true));
        //         }
        //         upToDateIndi = localicedIndi;
        //       }
        //     }
        //   }
        //   return upToDateIndi;
        //
        let up_to_date_indi = calc_alg_context.get_up_to_date_individual_by_id(indi_id);
        if up_to_date_indi.is_some() {
            // HIT: the individual-node vector already holds this individual — on a
            // retained class job that is EVERY ABox individual, COW-referenced
            // from the deterministic consistency base. Konclude's create path
            // below (cpp 22513-22580, with the backend-cache initialization at
            // 22524-22527) is therefore never taken, which is why the reuse
            // activation cannot live here alone.
            //
            // Instrumentation ONLY: a lazy id RESOLUTION is not a
            // "reached/influenced" — `isNominalIndividualNodeAvailable` (u16) and
            // the merge/link resolvers hit this path for nodes no rule touches.
            // Activating here would schedule the recorded model of every
            // individual the search merely looks up. The activation is done at the
            // point the node is actually processed
            // (`u03::individual_node_initializing`). This counter says how many
            // such resolutions carried an undecided association, i.e. how much
            // reuse the eager alternative would have scheduled.
            let undecided_association =
                match self.native_nominal_tag_for_node(up_to_date_indi, calc_alg_context) {
                    Some(tag) if !self.native_reuse_activated_individuals.contains(&tag) => self
                        .native_nominal_backend_replay
                        .get(&tag)
                        .map(|replay| replay.association_present && replay.has_reusable_elements)
                        .unwrap_or(false),
                    _ => false,
                };
            if undecided_association {
                self.native_reuse_lazy_lookup_hit_count += 1;
            }
            return up_to_date_indi;
        }
        if indi_id > 0 {
            return NodeId::NONE;
        }

        let individual_id = -indi_id;
        let mut individual = calc_alg_context
            .ontology_arenas()
            .individual_iter()
            .enumerate()
            .find_map(|(idx, indi)| {
                (indi.get_individual_id() == individual_id)
                    .then_some(IndividualId::new(idx as Cint64))
            })
            .unwrap_or(IndividualId::NONE);
        if individual.is_none() {
            individual =
                self.create_new_temporary_nominal_individual(individual_id, calc_alg_context);
        }
        if individual.is_none() {
            return NodeId::NONE;
        }

        self.track_individual_referred_dependence(indi_id, calc_alg_context);

        // Konclude obtains this from the task's already-initialised base
        // dependency node. Native bridge probes construct that task spine
        // lazily, so materialise the same independent base track point before
        // adding the nominal and cached assertion concepts.
        let dep_track_point = calc_alg_context.get_or_create_base_dependency_track_point();
        let localiced_indi = calc_alg_context
            .process_context_mut()
            .alloc_node(IndividualProcessNode::new(Id::NONE));
        {
            let role_assertion_creation_id = calc_alg_context
                .processing_data_box_mut()
                .next_role_assertion_creation_id(true);
            calc_alg_context
                .process_context_mut()
                .node_mut(localiced_indi)
                .set_dependency_track_point(dep_track_point)
                .set_nominal_individual(individual)
                .set_individual_type(IndividualType::Nominal)
                .set_individual_node_id(indi_id)
                .set_role_assertion_creation_id(role_assertion_creation_id)
                .set_nominal_individual_triples_assertions(true);
        }
        let (assertion_roles, reverse_assertion_roles) = {
            let individual_ref = calc_alg_context.ontology_arenas().individual(individual);
            (
                individual_ref.get_assertion_role_linker().to_vec(),
                individual_ref.get_reverse_assertion_role_linker().to_vec(),
            )
        };
        calc_alg_context
            .process_context_mut()
            .node_mut(localiced_indi)
            .set_assertion_role_assertions(assertion_roles)
            .set_reverse_assertion_role_assertions(reverse_assertion_roles);
        calc_alg_context
            .processing_data_box_mut()
            .individual_process_node_vector_mut()
            .set_local_data(indi_id, localiced_indi);

        // The value-backed forward/reverse assertion chains above are the
        // pointer-copy equivalent for native representative tasks. Data and
        // incremental assertion linkers remain on their existing paths.

        // W3-DEFER[api]: no live databox slot for
        // `getUniversalConnectionNominalValueConcept` exists yet.
        let nominal_concept = calc_alg_context
            .ontology_arenas()
            .individual(individual)
            .get_individual_nominal_concept();
        if nominal_concept.is_some() {
            let mut localiced_indi_mut = localiced_indi;
            self.add_concept_to_individual(
                nominal_concept,
                false,
                &mut localiced_indi_mut,
                dep_track_point,
                true,
                true,
                calc_alg_context,
            );
        }
        // Konclude's representative-computation jobs can begin with selected
        // roots and materialise other individuals lazily. Rust's authoritative
        // consistency task initializes every ABox individual, but later
        // classification probes can still enter through this lazy loader.
        // Consume the same typed association/assertion sidecar so lazy and
        // eager loads have identical deterministic input.
        let mut native_expansion_blocked = false;
        if let Some(replay) = self
            .native_nominal_backend_replay
            .get(&individual_id)
            .cloned()
        {
            // Konclude keeps the ontology assertion-concept linker on every
            // lazily materialized individual. Representative batches may
            // discover an incomplete neighbour that was not one of the
            // selected roots, so assertions cannot be left to the root
            // initializer.
            for &(concept, negated) in &replay.asserted_concepts {
                self.add_concept_to_individual_skip_and_processing(
                    concept,
                    negated,
                    localiced_indi,
                    dep_track_point,
                    true,
                    true,
                    false,
                    calc_alg_context,
                );
                if calc_alg_context.has_pending_signal() {
                    break;
                }
            }
            for &(concept, negated) in &replay.deterministic_cached_concepts {
                self.add_concept_to_individual_skip_and_processing(
                    concept,
                    negated,
                    localiced_indi,
                    dep_track_point,
                    true,
                    false,
                    false,
                    calc_alg_context,
                );
                if calc_alg_context.has_pending_signal() {
                    break;
                }
            }
            native_expansion_blocked = !calc_alg_context.has_pending_signal()
                && replay.expansion_blocking_candidate
                && self.conf_allow_backend_successor_expansion_blocking
                && !calc_alg_context
                    .process_context()
                    .node(localiced_indi)
                    .has_processing_restriction_flags(
                        IndividualProcessNode::PRF_INVALIDBLOCKINGORCACHING,
                    )
                && self.native_replay_concepts_synchronized(
                    localiced_indi,
                    &replay,
                    calc_alg_context,
                );
            let native_neighbour_blocked = !calc_alg_context.has_pending_signal()
                && replay.neighbour_expansion_blocking_candidate
                && self.conf_allow_backend_neighbour_expansion_blocking
                && !calc_alg_context
                    .process_context()
                    .node(localiced_indi)
                    .has_processing_restriction_flags(
                        IndividualProcessNode::PRF_INVALIDBLOCKINGORCACHING,
                    );
            if native_neighbour_blocked {
                calc_alg_context
                    .process_context_mut()
                    .node_mut(localiced_indi)
                    .add_processing_restriction_flags(
                        IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDNEIGHBOUREXPANSIONBLOCKED
                            | IndividualProcessNode::PRF_RETESTBACKENDSYNCHRONIZATIONDUEDIRECTMODIFIED,
                    );
            }
            if native_expansion_blocked {
                calc_alg_context
                    .process_context_mut()
                    .node_mut(localiced_indi)
                    .add_processing_restriction_flags(
                        IndividualProcessNode::PRF_SYNCHRONIZEDBACKEND
                            | IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDSUCCESSOREXPANSIONBLOCKED
                            | IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDINDIRECTNOMINALEXPANSIONBLOCKED,
                    );
            } else if !native_neighbour_blocked
                && !calc_alg_context.has_pending_signal()
                && !self.materialize_native_role_assertion_vectors(
                    localiced_indi,
                    dep_track_point,
                    calc_alg_context,
                )
            {
                calc_alg_context.raise_stop(false);
            }
            if !native_expansion_blocked
                && !native_neighbour_blocked
                && !calc_alg_context.has_pending_signal()
                && !replay.role_assertions.is_empty()
                && calc_alg_context
                    .process_context()
                    .node(localiced_indi)
                    .assertion_role_assertions()
                    .is_empty()
            {
                // Fail closed on a malformed bridge payload: the replay
                // journal and the ontology individual's value chain must agree.
                calc_alg_context.raise_stop(false);
            }
            if replay.association_present {
                calc_alg_context
                    .process_context_mut()
                    .node_mut(localiced_indi)
                    .set_nominal_individual_representative_backend_data_loaded(true);
            }

            // `initializeIndividualNodeWithBackendCache`'s reuse activation
            // (cpp 22710-22771), the FIRST of Konclude's two activation sites
            // (cpp 22524-22527, the create path of this very method). The
            // association's four non-deterministic slots are the ONLY record of
            // the consistency model's branch choices for this individual — a
            // derived task starts from the DETERMINISTIC root, so without this
            // queueing the class jobs re-derive them disjunct by disjunct
            // (Stage 8/9: retained-ABox branch opens dominate the search).
            //
            // The gate itself (four-slot `hasReuseableElements`, the
            // late-reuse-activation databox flag, the fail-closed
            // representability requirement and the per-job one-shot) lives in
            // `u25::activate_backend_individual_expansion_reuse`, which the
            // SECOND site (`u03::individual_node_initializing`, cpp 8713-8730)
            // shares — a retained class job reaches only that one, since the ABox
            // node vector is COW-inherited and no individual is ever materialized
            // here.
            self.activate_backend_individual_expansion_reuse(localiced_indi, calc_alg_context);
        }

        if self.opt_consistence_node_marking {
            calc_alg_context
                .process_context_mut()
                .node_mut(localiced_indi)
                .add_processing_restriction_flags(
                    IndividualProcessNode::PRF_CONSNODEPREPARATIONINDINODE,
                );
        }

        if !self.opt_incremental_compatible_expansion {
            let mut expansion_blocked = native_expansion_blocked;
            if !expansion_blocked
                && self
                    .load_individual_node_data_from_backend_cache(localiced_indi, calc_alg_context)
            {
                calc_alg_context
                    .process_context_mut()
                    .node_mut(localiced_indi)
                    .set_nominal_individual_representative_backend_data_loaded(true);
                // W6-DEFER[api]: `initializeIndividualNodeWithBackendCache` and
                // `tryEstablishExpansionBlockingWithBackendCacheSynchronisation`.
            }
            if !expansion_blocked && !calc_alg_context.has_pending_signal() {
                self.add_individual_to_processing_queue(localiced_indi, calc_alg_context);
            }
        } else {
            let inc_exp_id = calc_alg_context
                .processing_data_box()
                .incremental_expansion_id();
            let exp_id = calc_alg_context
                .processing_data_box_mut()
                .next_incremental_individual_expansion_id(true);
            calc_alg_context
                .process_context_mut()
                .node_mut(localiced_indi)
                .set_incremental_expansion_id(inc_exp_id)
                .add_processing_restriction_flags(IndividualProcessNode::PRF_INCREMENTALEXPANDING);
            let exp_data = calc_alg_context
                .process_context_mut()
                .node_incremental_expansion_data(localiced_indi, true);
            calc_alg_context
                .process_context_mut()
                .inc_exp_data_mut(exp_data)
                .set_expansion_id(exp_id);
        }

        localiced_indi
    }

    // =======================================================================
    // getPropagationSteeringController  (cpp 25707–25723).
    // =======================================================================

    /// Port of `getPropagationSteeringController`. cpp 25707–25723.
    pub fn get_propagation_steering_controller(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> PropagationSteeringController {
        // answererMessageAdapter = ctx->getSatisfiableCalculationTask()->getSatisfiableAnswererBindingPropagationAdapter();
        // if (answererMessageAdapter) {
        //   propagationSteeringController = answererMessageAdapter->getAnswererPropagationSteeringController();
        //   if (propagationSteeringController) return propagationSteeringController;
        // }
        // answererPropMessageAdapter = ctx->getSatisfiableCalculationTask()->getSatisfiableAnswererInstancePropagationMessageAdapter();
        // if (answererPropMessageAdapter) {
        //   propagationSteeringController = answererPropMessageAdapter->getAnswererPropagationSteeringController();
        //   if (propagationSteeringController) return propagationSteeringController;
        // }
        // return nullptr;
        //
        // W6-DEFER[api]: the `CSatisfiableCalculationTask` answerer binding-propagation /
        // instance-propagation message adapters and their `getAnswererPropagationSteeringController`
        // are the Task / answerer-message subsystem (W6); none reachable here. The two
        // null-guarded fall-throughs collapse to the C++ default of `nullptr`.
        let _ = calc_alg_context;
        INVALID
    }

    // =======================================================================
    // getLocalizedIndividual overloads + successor/ancestor (cpp 26412–26488).
    // =======================================================================

    /// Port of `getLocalizedIndividual(cint64 indiID, CCalculationAlgorithmContextBase*)`.
    /// cpp 26412–26414. KONCLUDE-PORT-NOTE[overload]: the `cint64` overload —
    /// pure delegation: `getLocalizedIndividual(getUpToDateIndividual(indiID,ctx),false,ctx)`.
    pub fn get_localized_individual_by_id(
        &mut self,
        indi_id: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        let up_to_date = self.get_up_to_date_individual_by_id(indi_id, calc_alg_context);
        self.get_localized_individual(up_to_date, false, calc_alg_context)
    }

    /// Port of `getLocalizedIndividual(CIndividualProcessNode* indi, bool updateIndividual,
    /// CCalculationAlgorithmContextBase*)`. cpp 26416–26444.
    pub fn get_localized_individual(
        &mut self,
        indi: NodeId,
        update_individual: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        // PORT-PENDING: faithful transcription of cpp 26416–26444. Outline:
        //
        //   if (!indi->isLocalizationTagUpToDate(ctx->getUsedProcessTagger()->getCurrentLocalizationTag())) {
        //     if (updateIndividual) indi = self.get_up_to_date_individual(indi, ctx);          // node overload sibling
        //     if (!indi->isLocalizationTagUpToDate(...)) {
        //       STATINC(INDINODELOCALIZEDLOADCOUNT, ctx);
        //       indiProcNodeVec = ctx->getProcessingDataBox()->getIndividualProcessNodeVector();
        //       localicedIndi = ctx.used_process_context_mut().alloc_node(IndividualProcessNode::new(procCtx));
        //       localicedIndi.init_individual_process_node(indi);
        //       indiProcNodeVec->setLocalData(localicedIndi.individual_node_id(), localicedIndi);
        //       if (ctx->hasCompletionGraphCachedIndividualNodes() && mConfCompletionGraphCaching) {
        //         if (localicedIndi.individual_node_id() <= ctx.max_completion_graph_cached_individual_node_id()) {
        //           if (indi->getLocalizationTag() <= ctx.completion_graph_cached_localization_tag()) {
        //             trackIndividualReferredDependence(indi.individual_node_id(), ctx);          // dep sibling
        //             localicedIndi.clear_processing_queued();
        //             localicedIndi.clear_processing_restriction_flags(PRF_CACHEDCOMPUTEDTYPESADDED);
        //             localicedIndi.add_processing_restriction_flags(PRF_COMPLETIONGRAPHCACHED);
        //           }
        //         }
        //       }
        //       return localicedIndi;
        //     }
        //   }
        //   return indi;
        //
        // NOW LIVE: superseded by `ctx.get_localized_individual` (node-resolution
        // keystone) — the tagger reader + node arena + databox node-vector setLocalData
        // + `init_individual_process_node` are wired there. The completion-graph-cache
        // re-flag branch (.cpp 26430–26439) stays deferred inside the keystone.
        calc_alg_context.get_localized_individual(indi, update_individual)
    }

    /// Port of `getSuccessorIndividual`. cpp 26446–26461.
    /// KONCLUDE-PORT-NOTE[ownership]: `CIndividualProcessNode*& indi` → `&mut NodeId`;
    /// `CIndividualLinkEdge* link` → `EdgeId`.
    pub fn get_successor_individual(
        &mut self,
        indi: &mut NodeId,
        link: EdgeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        // PORT-PENDING: faithful transcription of cpp 26446–26461. Outline:
        //
        //   succIndi = nullptr;
        //   if (link->isLocalizationTagUpToDate(ctx->getUsedProcessTagger()->getCurrentLocalizationTag())) {
        //     succIndi = link->getOppositeIndividual(indi);
        //   } else {
        //     STATINC(INDINODEUPDATELOADCOUNT, ctx);
        //     succIndi = link->getOppositeIndividual(indi);
        //     if (!succIndi->isLocalizationTagUpToDate(...) && succIndi->isRelocalized()) {       // is_relocalized() IS live (pn1)
        //       succIndiId = link->getOppositeIndividualID(indi);
        //       indiProcNodeVec = ctx->getProcessingDataBox()->getIndividualProcessNodeVector();
        //       succIndi = indiProcNodeVec->getData(succIndiId);
        //     }
        //   }
        //   return succIndi;
        //
        // NOW LIVE: superseded by `ctx.get_successor_individual` (node-resolution
        // keystone) — the edge localisation-tag protocol + opposite-individual
        // resolution + databox node-vector are wired there.
        calc_alg_context.get_successor_individual(indi, link)
    }

    /// Port of `getLocalizedSuccessorIndividual`. cpp 26464–26477.
    pub fn get_localized_successor_individual(
        &mut self,
        indi: &mut NodeId,
        link: EdgeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        // PORT-PENDING: faithful transcription of cpp 26464–26477. Outline:
        //
        //   succIndi = nullptr;
        //   if (link->isLocalizationTagUpToDate(ctx->getUsedProcessTagger()->getCurrentLocalizationTag())) {
        //     succIndi = link->getOppositeIndividual(indi);
        //   } else {
        //     STATINC(INDINODEUPDATELOADCOUNT, ctx);
        //     succIndiId = link->getOppositeIndividualID(indi);
        //     indiProcNodeVec = ctx->getProcessingDataBox()->getIndividualProcessNodeVector();
        //     succIndi = indiProcNodeVec->getData(succIndiId);
        //     succIndi = self.get_localized_individual(succIndi, false, ctx);
        //   }
        //   return succIndi;
        //
        // NOW LIVE: superseded by `ctx.get_localized_successor_individual`
        // (node-resolution keystone), which resolves the opposite individual through
        // the node vector and then localises it.
        calc_alg_context.get_localized_successor_individual(indi, link)
    }

    /// Port of `getAncestorIndividual`. cpp 26480–26488.
    pub fn get_ancestor_individual(
        &mut self,
        indi: &mut NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        // ancIndi = nullptr;
        // ancLink = indi->getAncestorLink();
        // if (ancLink) ancIndi = getSuccessorIndividual(indi, ancLink, ctx);
        // return ancIndi;
        //
        // NOW LIVE: superseded by `ctx.get_ancestor_individual` (node-resolution
        // keystone), which follows the ancestor link through `get_successor_individual`.
        calc_alg_context.get_ancestor_individual(indi)
    }

    // =======================================================================
    // addConceptToIndividual + …ReturnConceptDescriptor (cpp 26725–26782).
    // =======================================================================

    /// Port of `addConceptToIndividual`. cpp 26725–26753.
    /// KONCLUDE-PORT-NOTE[ownership]: `CConcept* addingConcept` → `ConceptId`;
    /// `CIndividualProcessNode*& processIndi` → `&mut NodeId`.
    pub fn add_concept_to_individual(
        &mut self,
        adding_concept: ConceptId,
        negate: bool,
        process_indi: &mut NodeId,
        dependency_track_point: TrackPointId,
        allow_preprocessing: bool,
        allow_initalization: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // With dependency building ON, an untracked insertion would poison
        // every clash analysis it later participates in (tracking ERROR) —
        // substitute the INDEPENDENT base dependency track point, exactly
        // Konclude's base-assertion tracking.
        //
        // CAUTION[ddb-soundness]: a NONE here on a RULE path (not a base
        // seed) means the caller's dependency threading is unported — the
        // substitution then paints a branch-dependent addition as
        // independent, and a clash over it traces to branching level 0 →
        // wrong root cancellation (measured: 12653 spurious=4 under DDB).
        // The diagnostic below surfaces such callers so their faithful track
        // points get threaded.
        if self.conf_build_dependencies
            && dependency_track_point.is_none()
            && self.ddb_analysis_dumps < 3
            && std::env::var_os("KM_BRIDGE_PROGRESS").is_some()
        {
            self.ddb_analysis_dumps += 1;
            eprintln!(
                "NONE-TP-ADD(single) c={} at:\n{}",
                calc_alg_context
                    .ontology_arenas()
                    .concept(adding_concept)
                    .get_concept_tag(),
                std::backtrace::Backtrace::force_capture()
            );
        }
        let dependency_track_point =
            if self.conf_build_dependencies && dependency_track_point.is_none() {
                calc_alg_context.get_or_create_base_dependency_track_point()
            } else {
                dependency_track_point
            };
        // KM_BRIDGE_WATCH_TAG=<tag>: print the call path of every POSITIVE
        // addition of that concept tag (provenance for over-derivation hunts).
        if let Ok(w) = std::env::var("KM_BRIDGE_WATCH_TAG") {
            if let Ok(wt) = w.parse::<Cint64>() {
                let tag = calc_alg_context
                    .ontology_arenas()
                    .concept(adding_concept)
                    .get_concept_tag();
                if tag == wt && !negate && self.ddb_analysis_dumps < 6 {
                    self.ddb_analysis_dumps += 1;
                    eprintln!(
                        "WATCH-TAG {} pos add to node {} at:\n{}",
                        wt,
                        calc_alg_context
                            .process_context()
                            .node(*process_indi)
                            .individual_node_id(),
                        std::backtrace::Backtrace::force_capture()
                    );
                }
            }
        }
        // KM_BRIDGE_WATCH_NEGTAG=<tag>: the negated-add twin of WATCH_TAG (e.g.
        // tag 1 negated = a ⊥ insertion), with the dependency track point id —
        // provenance for wrong-root-cancel hunts.
        if let Ok(w) = std::env::var("KM_BRIDGE_WATCH_NEGTAG") {
            if let Ok(wt) = w.parse::<Cint64>() {
                let tag = calc_alg_context
                    .ontology_arenas()
                    .concept(adding_concept)
                    .get_concept_tag();
                if tag == wt && negate && self.ddb_analysis_dumps < 6 {
                    self.ddb_analysis_dumps += 1;
                    let bt = std::backtrace::Backtrace::force_capture().to_string();
                    let frames: Vec<&str> = bt
                        .lines()
                        .filter(|l| l.contains("konclude_ht::completion::u"))
                        .take(6)
                        .collect();
                    eprintln!(
                        "WATCH-NEGTAG ¬{} add to node {} under tp={:?} via {}",
                        wt,
                        calc_alg_context
                            .process_context()
                            .node(*process_indi)
                            .individual_node_id(),
                        dependency_track_point,
                        frames.join(" <- ")
                    );
                }
            }
        }
        // KM_BRIDGE_WATCH_NODE=<id>: print the first ~24 POSITIVE NAMED-tag
        // additions to that node in arrival order with a short call path —
        // catches the ENTRY POINT of an over-derivation cascade.
        if let Ok(w) = std::env::var("KM_BRIDGE_WATCH_NODE") {
            if let Ok(wn) = w.parse::<Cint64>() {
                let node_id = calc_alg_context
                    .process_context()
                    .node(*process_indi)
                    .individual_node_id();
                let tag = calc_alg_context
                    .ontology_arenas()
                    .concept(adding_concept)
                    .get_concept_tag();
                if node_id == wn
                    && !negate
                    && (10..320).contains(&tag)
                    && self.ddb_analysis_dumps < 24
                {
                    self.ddb_analysis_dumps += 1;
                    let bt = std::backtrace::Backtrace::force_capture().to_string();
                    let frames: Vec<&str> = bt
                        .lines()
                        .filter(|l| l.contains("konclude_ht::completion::u"))
                        .take(3)
                        .collect();
                    eprintln!("WATCH-NODE {wn} += {tag} via {}", frames.join(" <- "));
                }
            }
        }
        // conProQueue = processIndi->getConceptProcessingQueue(true);
        // conLabelSet = processIndi->getReapplyConceptLabelSet(true);
        // W5: the create branch's arena allocation cannot run from the superseded
        // `&mut self` node getters (they return `Id::NONE`); route through the
        // context-threaded lazy getters (W3b/W8.1) that DO allocate.
        let con_pro_queue = calc_alg_context
            .process_context_mut()
            .node_concept_processing_queue(*process_indi, true);
        let con_label_set = calc_alg_context
            .process_context_mut()
            .node_reapply_concept_label_set(*process_indi);
        // KONCLUDE_ASSERT_X(dependencyTrackPoint / addingConcept) — debug asserts, elided.

        // conceptDescriptor = createConceptDescriptor(ctx);
        // conceptDescriptor->initConceptDescriptor(addingConcept, negate, dependencyTrackPoint);
        let concept_descriptor = self.create_concept_descriptor(calc_alg_context);
        self.init_concept_descriptor_fields(
            concept_descriptor,
            adding_concept,
            negate,
            dependency_track_point,
            calc_alg_context,
        );
        let mut reapply_it = CondensedReapplyQueueIterator::new();
        let contained = self.insert_concepts_to_individual_concept_set(
            concept_descriptor,
            dependency_track_point,
            process_indi,
            con_label_set,
            Some(&mut reapply_it),
            allow_initalization,
            calc_alg_context,
        );
        if !contained {
            // W3-DEFER[macro]: STATINC(CONCEPTSADDEDINDINODELABELSETCOUNT, ctx);
            self.stat_con_des_insertion_count += 1;
            self.add_blocking_core_concept(
                concept_descriptor,
                *process_indi,
                con_label_set,
                calc_alg_context,
            );
            self.set_individual_node_concept_label_set_modified(process_indi, calc_alg_context);
            // KONCLUDE-PORT-NOTE[overload]: the C++ `addConceptPreprocessedToProcessingQueue`
            // call here is the `bool allowPreprocessing` overload (cpp 27228) — ported as
            // the `…_skip` sibling (u04); the `cint64 bindingCount` overload keeps the bare name.
            self.add_concept_preprocessed_to_processing_queue_skip(
                concept_descriptor,
                dependency_track_point,
                con_pro_queue,
                *process_indi,
                allow_preprocessing,
                calc_alg_context,
                INVALID,
            );
            if reapply_it.has_next() {
                self.apply_reapply_queue_concepts_condensed_iterator(
                    *process_indi,
                    reapply_it,
                    calc_alg_context,
                );
            }
        } else {
            self.stat_con_des_contained_count += 1;
            self.release_concept_descriptor(concept_descriptor, calc_alg_context);
        }
    }

    /// Port of `addConceptToIndividualReturnConceptDescriptor`. cpp 26757–26782.
    pub fn add_concept_to_individual_return_concept_descriptor(
        &mut self,
        adding_concept: ConceptId,
        negate: bool,
        process_indi: &mut NodeId,
        dependency_track_point: TrackPointId,
        allow_preprocessing: bool,
        allow_initalization: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> ConDescId {
        let con_pro_queue = calc_alg_context
            .process_context_mut()
            .node_concept_processing_queue(*process_indi, true);
        let con_label_set = calc_alg_context
            .process_context_mut()
            .node_reapply_concept_label_set(*process_indi);
        // KONCLUDE_ASSERT_X(…) — debug asserts, elided.

        let concept_descriptor = self.create_concept_descriptor(calc_alg_context);
        self.init_concept_descriptor_fields(
            concept_descriptor,
            adding_concept,
            negate,
            dependency_track_point,
            calc_alg_context,
        );
        let mut reapply_it = CondensedReapplyQueueIterator::new();
        // NB: this variant does NOT branch on `contained` — it always treats the
        // concept as freshly inserted (the C++ ignores the return).
        self.insert_concepts_to_individual_concept_set(
            concept_descriptor,
            dependency_track_point,
            process_indi,
            con_label_set,
            Some(&mut reapply_it),
            allow_initalization,
            calc_alg_context,
        );
        self.stat_con_des_insertion_count += 1;

        // W3-DEFER[macro]: STATINC(CONCEPTSADDEDINDINODELABELSETCOUNT, ctx);
        self.add_blocking_core_concept(
            concept_descriptor,
            *process_indi,
            con_label_set,
            calc_alg_context,
        );
        self.set_individual_node_concept_label_set_modified(process_indi, calc_alg_context);
        // KONCLUDE-PORT-NOTE[overload]: `bool allowPreprocessing` overload (cpp 27228) → `…_skip` sibling.
        self.add_concept_preprocessed_to_processing_queue_skip(
            concept_descriptor,
            dependency_track_point,
            con_pro_queue,
            *process_indi,
            allow_preprocessing,
            calc_alg_context,
            INVALID,
        );
        if reapply_it.has_next() {
            self.apply_reapply_queue_concepts_condensed_iterator(
                *process_indi,
                reapply_it,
                calc_alg_context,
            );
        }
        concept_descriptor
    }

    // =======================================================================
    // Modification flags + label-set modification tests (cpp 26786–26802).
    // =======================================================================

    /// Port of `setIndividualNodeAncestorConnectionModified`. cpp 26786–26788.
    pub fn set_individual_node_ancestor_connection_modified(
        &mut self,
        indi: &mut NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // propagateIndividualNodeModified(indi, ctx);
        self.propagate_individual_node_modified(indi, calc_alg_context);
    }

    /// Port of `setIndividualNodeConceptLabelSetModified`. cpp 26790–26796.
    pub fn set_individual_node_concept_label_set_modified(
        &mut self,
        indi: &mut NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let con_label_set = calc_alg_context
            .process_context_mut()
            .node_reapply_concept_label_set(*indi);
        let tag = {
            let process_context = calc_alg_context.process_context_mut();
            process_context
                .used_process_tagger_mut()
                .inc_concept_label_set_modification_tag();
            process_context
                .used_process_tagger()
                .get_current_concept_label_set_modification_tag()
        };
        calc_alg_context
            .process_context_mut()
            .label_set_mut(con_label_set)
            .modification_tag
            .update_concept_label_set_modification_tag(tag);
        calc_alg_context
            .base
            .set_min_modification_individual_candidate(*indi);
        self.propagate_individual_node_modified(indi, calc_alg_context);
    }

    /// Port of `isIndividualNodeConceptLabelSetModified`. cpp 26800–26802.
    pub fn is_individual_node_concept_label_set_modified(
        &mut self,
        indi: &mut NodeId,
        mod_tag: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let label_set = calc_alg_context
            .process_context()
            .node(*indi)
            .use_reapply_con_label_set;
        if label_set.is_none() {
            return false;
        }
        calc_alg_context
            .process_context()
            .label_set(label_set)
            .is_concept_label_set_modification_tag_up_to_date(mod_tag)
    }

    // =======================================================================
    // Concept-descriptor pool (cpp 26809–26824).
    // =======================================================================

    /// Port of `createConceptDescriptor`. cpp 26809–26817.
    pub fn create_concept_descriptor(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> ConDescId {
        // processingDataBox = ctx->getUsedProcessingDataBox();
        // conDes = processingDataBox->takeRemainingConceptDescriptor();
        // if (!conDes) conDes = CObjectAllocator<CConceptDescriptor>::allocateAndConstruct(taskMemMan);
        // return conDes;
        let con_des = calc_alg_context
            .processing_data_box_mut()
            .take_remaining_concept_descriptor();
        if con_des == ConDescId::NONE {
            // KONCLUDE-PORT-NOTE[memory-pool]: the pool allocator becomes an arena
            // allocation from the per-test concept-descriptor arena.
            calc_alg_context
                .process_context_mut()
                .alloc_con_desc(super::super::process::descriptor::ConceptDescriptor::new())
        } else {
            con_des
        }
    }

    /// Port of `releaseConceptDescriptor`. cpp 26820–26824.
    pub fn release_concept_descriptor(
        &mut self,
        con_des: ConDescId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // conDes->clearNext();
        // processingDataBox = ctx->getUsedProcessingDataBox();
        // processingDataBox->addRemainingConceptDescriptor(conDes);
        calc_alg_context
            .process_context_mut()
            .con_desc_mut(con_des)
            .set_next(ConDescId::NONE); // clearNext()
        calc_alg_context
            .processing_data_box_mut()
            .add_remaining_concept_descriptor(con_des);
    }

    // =======================================================================
    // addConceptsToIndividual linker overloads (cpp 26829, 27026, 27068, 27110)
    // + insertConceptsToIndividualConceptSet (cpp 26925).
    // =======================================================================

    /// Port of `addConceptsToIndividual(CSortedNegLinker<CConcept*>* conceptAddLinkerIt, …)`.
    /// cpp 26829–26869. The primary linker overload (keeps the bare name).
    /// KONCLUDE-PORT-NOTE[overload]: the `CSortedNegLinker<CConcept*>` chain →
    /// `&[NegLink<ConceptId>]` (head→tail). This overload (and ONLY this one)
    /// increments `conCount` and writes it back through `concept_count`.
    pub fn add_concepts_to_individual(
        &mut self,
        concept_add_linker_it: &[NegLink<ConceptId>],
        negate: bool,
        process_indi: &mut NodeId,
        dependency_track_point: TrackPointId,
        allow_preprocessing: bool,
        allow_initalization: bool,
        concept_count: Option<&mut Cint64>,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // Untracked-insertion substitution — see `add_concept_to_individual`
        // (including the CAUTION[ddb-soundness] note).
        if self.conf_build_dependencies
            && dependency_track_point.is_none()
            && self.ddb_analysis_dumps < 3
            && std::env::var_os("KM_BRIDGE_PROGRESS").is_some()
        {
            self.ddb_analysis_dumps += 1;
            eprintln!(
                "NONE-TP-ADD(multi n={}) at:\n{}",
                concept_add_linker_it.len(),
                std::backtrace::Backtrace::force_capture()
            );
        }
        let dependency_track_point =
            if self.conf_build_dependencies && dependency_track_point.is_none() {
                calc_alg_context.get_or_create_base_dependency_track_point()
            } else {
                dependency_track_point
            };
        // W8: route the node's concept queue + reapply label set through the
        // context-threaded lazy getters (W3b/W8.1) — the superseded `&mut self` node
        // getters return `Id::NONE` (they cannot run the arena allocation), so the
        // operand inserts below would otherwise hit no real label set. This mirrors
        // the W5 fix already applied to `add_concept_to_individual`.
        let con_pro_queue = calc_alg_context
            .process_context_mut()
            .node_concept_processing_queue(*process_indi, true);
        // KONCLUDE_ASSERT_X(dependencyTrackPoint) — elided.

        let mut con_count: Cint64 = 0;
        let con_label_set = calc_alg_context
            .process_context_mut()
            .node_reapply_concept_label_set(*process_indi);
        for link in concept_add_linker_it {
            let concept = link.target;
            let con_neg = link.negated ^ negate;
            // KONCLUDE_ASSERT_X(concept) — elided.
            self.add_one_concept_to_individual_concept_set(
                concept,
                con_neg,
                process_indi,
                dependency_track_point,
                con_label_set,
                con_pro_queue,
                allow_preprocessing,
                allow_initalization,
                calc_alg_context,
            );
            con_count += 1;
        }
        if let Some(out) = concept_count {
            *out = con_count;
        }
    }

    /// Port of `addConceptsToIndividual(CConceptAssertionLinker* conceptAddLinkerIt, …)`.
    /// cpp 27026–27064. KONCLUDE-PORT-NOTE[overload]: the `CConceptAssertionLinker`
    /// chain → `&[NegLink<ConceptId>]`. NB this overload computes `conCount` but
    /// never increments it (the C++ loop has no `++conCount`), so `*conceptCount`
    /// is always written `0` — ported EXACTLY.
    pub fn add_concepts_to_individual_from_assertion_linker(
        &mut self,
        concept_add_linker_it: &[NegLink<ConceptId>],
        negate: bool,
        process_indi: &mut NodeId,
        dependency_track_point: TrackPointId,
        allow_preprocessing: bool,
        allow_initalization: bool,
        concept_count: Option<&mut Cint64>,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let con_pro_queue = calc_alg_context
            .process_context_mut()
            .node_mut(*process_indi)
            .get_concept_processing_queue(true);
        let con_count: Cint64 = 0; // C++ never increments conCount in this overload.
        let con_label_set = calc_alg_context
            .process_context_mut()
            .node_mut(*process_indi)
            .get_reapply_concept_label_set(true);
        for link in concept_add_linker_it {
            let concept = link.target;
            let con_neg = link.negated ^ negate;
            self.add_one_concept_to_individual_concept_set(
                concept,
                con_neg,
                process_indi,
                dependency_track_point,
                con_label_set,
                con_pro_queue,
                allow_preprocessing,
                allow_initalization,
                calc_alg_context,
            );
        }
        if let Some(out) = concept_count {
            *out = con_count;
        }
    }

    /// Port of `addConceptsToIndividual(CXNegLinker<CConcept*>* conceptAddLinkerIt, …)`.
    /// cpp 27068–27106. KONCLUDE-PORT-NOTE[overload]: `CXNegLinker<CConcept*>` chain
    /// → `&[NegLink<ConceptId>]`. Same as the assertion-linker overload, this one
    /// also never increments `conCount`.
    pub fn add_concepts_to_individual_from_neg_linker(
        &mut self,
        concept_add_linker_it: &[NegLink<ConceptId>],
        negate: bool,
        process_indi: &mut NodeId,
        dependency_track_point: TrackPointId,
        allow_preprocessing: bool,
        allow_initalization: bool,
        concept_count: Option<&mut Cint64>,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let con_pro_queue = calc_alg_context
            .process_context_mut()
            .node_mut(*process_indi)
            .get_concept_processing_queue(true);
        let con_count: Cint64 = 0; // C++ never increments conCount in this overload.
        let con_label_set = calc_alg_context
            .process_context_mut()
            .node_mut(*process_indi)
            .get_reapply_concept_label_set(true);
        for link in concept_add_linker_it {
            let concept = link.target;
            let con_neg = link.negated ^ negate;
            self.add_one_concept_to_individual_concept_set(
                concept,
                con_neg,
                process_indi,
                dependency_track_point,
                con_label_set,
                con_pro_queue,
                allow_preprocessing,
                allow_initalization,
                calc_alg_context,
            );
        }
        if let Some(out) = concept_count {
            *out = con_count;
        }
    }

    /// Port of `addConceptsToIndividual(CXSortedNegLinker<CConcept*>* conceptAddLinkerIt, …)`.
    /// cpp 27110–27148. KONCLUDE-PORT-NOTE[overload]: `CXSortedNegLinker<CConcept*>`
    /// chain → `&[NegLink<ConceptId>]`. Identical body to the `CXNegLinker` overload
    /// except the C++ reads `getData()` before the negation (immaterial); also never
    /// increments `conCount`.
    pub fn add_concepts_to_individual_from_sorted_neg_linker(
        &mut self,
        concept_add_linker_it: &[NegLink<ConceptId>],
        negate: bool,
        process_indi: &mut NodeId,
        dependency_track_point: TrackPointId,
        allow_preprocessing: bool,
        allow_initalization: bool,
        concept_count: Option<&mut Cint64>,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let con_pro_queue = calc_alg_context
            .process_context_mut()
            .node_mut(*process_indi)
            .get_concept_processing_queue(true);
        let con_count: Cint64 = 0; // C++ never increments conCount in this overload.
        let con_label_set = calc_alg_context
            .process_context_mut()
            .node_mut(*process_indi)
            .get_reapply_concept_label_set(true);
        for link in concept_add_linker_it {
            let concept = link.target;
            let con_neg = link.negated ^ negate;
            self.add_one_concept_to_individual_concept_set(
                concept,
                con_neg,
                process_indi,
                dependency_track_point,
                con_label_set,
                con_pro_queue,
                allow_preprocessing,
                allow_initalization,
                calc_alg_context,
            );
        }
        if let Some(out) = concept_count {
            *out = con_count;
        }
    }

    /// The shared inner body of the four `addConceptsToIndividual` linker overloads
    /// (the per-element create-descriptor / insert / not-contained / release block,
    /// cpp 26845–26864 and the byte-identical copies at 27041–27058 / 27083–27100 /
    /// 27125–27142). KONCLUDE-PORT-NOTE[overload]: factored out because the four C++
    /// overloads differ ONLY in their linker iteration; the per-concept work is
    /// literally identical. This is a port-internal helper, not a Konclude method.
    fn add_one_concept_to_individual_concept_set(
        &mut self,
        concept: ConceptId,
        con_neg: bool,
        process_indi: &mut NodeId,
        dependency_track_point: TrackPointId,
        con_label_set: LabelSetId,
        con_pro_queue: super::super::process::stubs::ConceptProcessingQueueId,
        allow_preprocessing: bool,
        allow_initalization: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // conceptDescriptor = createConceptDescriptor(ctx);
        // conceptDescriptor->initConceptDescriptor(concept, conNeg, dependencyTrackPoint);
        let concept_descriptor = self.create_concept_descriptor(calc_alg_context);
        self.init_concept_descriptor_fields(
            concept_descriptor,
            concept,
            con_neg,
            dependency_track_point,
            calc_alg_context,
        );
        let mut reapply_it = CondensedReapplyQueueIterator::new();
        let contained = self.insert_concepts_to_individual_concept_set(
            concept_descriptor,
            dependency_track_point,
            process_indi,
            con_label_set,
            Some(&mut reapply_it),
            allow_initalization,
            calc_alg_context,
        );
        if !contained {
            self.stat_con_des_insertion_count += 1;
            // W3-DEFER[macro]: STATINC(CONCEPTSADDEDINDINODELABELSETCOUNT, ctx);
            self.add_blocking_core_concept(
                concept_descriptor,
                *process_indi,
                con_label_set,
                calc_alg_context,
            );
            self.set_individual_node_concept_label_set_modified(process_indi, calc_alg_context);
            // KONCLUDE-PORT-NOTE[overload]: the C++ `addConceptPreprocessedToProcessingQueue`
            // call here is the `bool allowPreprocessing` overload (cpp 27228) — ported as
            // the `…_skip` sibling (u04); the `cint64 bindingCount` overload keeps the bare name.
            self.add_concept_preprocessed_to_processing_queue_skip(
                concept_descriptor,
                dependency_track_point,
                con_pro_queue,
                *process_indi,
                allow_preprocessing,
                calc_alg_context,
                INVALID,
            );
            if reapply_it.has_next() {
                self.apply_reapply_queue_concepts_condensed_iterator(
                    *process_indi,
                    reapply_it,
                    calc_alg_context,
                );
            }
        } else {
            self.stat_con_des_contained_count += 1;
            self.release_concept_descriptor(concept_descriptor, calc_alg_context);
        }
    }

    /// Port of `insertConceptsToIndividualConceptSet`. cpp 26925–27021.
    /// KONCLUDE-PORT-NOTE[ownership]: `CConceptDescriptor*` → `ConDescId`,
    /// `CReapplyConceptLabelSet*` → `LabelSetId`,
    /// `CCondensedReapplyQueueIterator*` → `Option<&mut CondensedReapplyQueueIterator>`.
    pub fn insert_concepts_to_individual_concept_set(
        &mut self,
        concept_descriptor: ConDescId,
        dependency_track_point: TrackPointId,
        process_indi: &mut NodeId,
        con_label_set: LabelSetId,
        reapply_it: Option<&mut CondensedReapplyQueueIterator>,
        allow_initalization: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // clashedConceptDescriptor = nullptr; clashedDependencyTrackPoint = nullptr;
        let mut clashed_concept_descriptor: ConDescId = Id::NONE;
        let mut clashed_dependency_track_point: TrackPointId = Id::NONE;

        // if (mConfConceptUnsatisfiabilitySaturatedTesting) {
        //   if (isConceptUnsatisfiabilitySaturated(conceptDescriptor->getConcept(), conceptDescriptor->isNegated(), ctx)) {
        //     clashConDesLinker = createClashedConceptDescriptor(nullptr, processIndi, conceptDescriptor, dependencyTrackPoint, ctx);
        //     throw CCalculationClashProcessingException(clashConDesLinker);
        //   }
        // }
        if self.conf_concept_unsatisfiability_saturated_testing {
            let con = calc_alg_context
                .process_context()
                .con_desc(concept_descriptor)
                .get_concept();
            let neg = calc_alg_context
                .process_context()
                .con_desc(concept_descriptor)
                .is_negated();
            if self.is_concept_unsatisfiability_saturated(con, neg, calc_alg_context) {
                let clash_con_des_linker = self.create_clashed_concept_descriptor(
                    Id::NONE,
                    process_indi,
                    concept_descriptor,
                    dependency_track_point,
                    calc_alg_context,
                );
                calc_alg_context.raise_clash(clash_con_des_linker);
                return false;
            }
        }

        // contained = conLabelSet->insertConceptGetClash(conceptDescriptor, dependencyTrackPoint,
        //                 reapplyIt, &clashedConceptDescriptor, &clashedDependencyTrackPoint);
        // W5: resolve the descriptor's real concept tag + negation against the arenas
        // (the label set cannot do it from `&mut self`), lift the label set out of the
        // arena so the `&ProcessContext` descriptor-negation resolver is free of the
        // `&mut` borrow, run the faithful clash insert, then restore the label set.
        let new_concept = calc_alg_context
            .process_context()
            .con_desc(concept_descriptor)
            .get_concept();
        let new_negated = calc_alg_context
            .process_context()
            .con_desc(concept_descriptor)
            .is_negated();
        let new_con_tag = calc_alg_context
            .ontology_arenas()
            .concept(new_concept)
            .get_concept_tag();
        let new_concept_identity =
            calc_alg_context.ontology_arenas().concept(new_concept) as *const _ as usize as Cint64;
        let watch_insert = std::env::var("KM_BRIDGE_WATCH_TAG")
            .ok()
            .and_then(|value| value.parse::<Cint64>().ok())
            == Some(new_con_tag)
            && !new_negated;
        if watch_insert {
            let dependency_track_point = calc_alg_context
                .process_context()
                .con_desc(concept_descriptor)
                .get_dependency_track_point();
            let dependency_branching_tag = dependency_track_point.is_some().then(|| {
                calc_alg_context
                    .process_context()
                    .track_point(dependency_track_point)
                    .get_branching_tag()
            });
            eprintln!(
                "WATCH-INSERT-TAG {} before node={} descriptor={} dependency={:?} branch={:?} allow_init={} at:\n{}",
                new_con_tag,
                calc_alg_context
                    .process_context()
                    .node(*process_indi)
                    .individual_node_id(),
                concept_descriptor.index(),
                dependency_track_point,
                dependency_branching_tag,
                allow_initalization,
                std::backtrace::Backtrace::force_capture(),
            );
        }
        // CReapplyConceptLabelSet::insertConceptGetClash prepends with
        // `mConceptDesLinker = conceptDescriptor->append(mConceptDesLinker)`.
        // Preserve that intrusive chain before lifting the label set out of
        // the process arena for the resolved tag/polarity lookup below.
        let previous_concept_descriptor = calc_alg_context
            .process_context()
            .label_set(con_label_set)
            .get_adding_sorted_concept_description_linker();
        calc_alg_context
            .process_context_mut()
            .con_desc_mut(concept_descriptor)
            .set_next(previous_concept_descriptor);
        let mut lifted_label_set = std::mem::replace(
            calc_alg_context
                .process_context_mut()
                .label_set_mut(con_label_set),
            ReapplyConceptLabelSet::default(),
        );
        let contained = {
            let pc = calc_alg_context.process_context();
            lifted_label_set.insert_concept_get_clash_resolved(
                concept_descriptor,
                new_concept,
                new_con_tag,
                new_negated,
                new_concept_identity,
                &|d| pc.con_desc(d).is_negated(),
                Some(&mut clashed_concept_descriptor),
                Some(&mut clashed_dependency_track_point),
            )
        };
        *calc_alg_context
            .process_context_mut()
            .label_set_mut(con_label_set) = lifted_label_set;
        if watch_insert {
            eprintln!(
                "WATCH-INSERT-TAG {} after node={} contained={}",
                new_con_tag,
                calc_alg_context
                    .process_context()
                    .node(*process_indi)
                    .individual_node_id(),
                contained,
            );
        }
        // The ls1 label set cannot resolve the stored descriptor's dependency
        // track point (`con_des_dep_track_point` is a ctx-less stub returning
        // NONE) — resolve it here, exactly the C++
        // `containedConDes->getDependencyTrackPoint()`. Without this every
        // insert-clash reported its contained partner UNTRACKED, which is a
        // tracking ERROR that aborted every `clashedBacktracking` analysis
        // (measured on ore_ont_541: ddb_marks=0, fallbacks=100%).
        if clashed_concept_descriptor.is_some() && clashed_dependency_track_point.is_none() {
            clashed_dependency_track_point = calc_alg_context
                .process_context()
                .con_desc(clashed_concept_descriptor)
                .get_dependency_track_point();
        }
        if !contained {
            if let Some(out) = reapply_it {
                *out = calc_alg_context
                    .process_context_mut()
                    .node_concept_reapply_iterator_by_tag(
                        *process_indi,
                        new_con_tag,
                        new_negated,
                        true,
                    );
            }
        }

        if !contained {
            // if (allowInitalization && !processIndi->getIndividualInitializationConcept())
            //     processIndi->setIndividualInitializationConcept(conceptDescriptor);
            if allow_initalization {
                let has_init = calc_alg_context
                    .process_context()
                    .node(*process_indi)
                    .individual_initialization_concept();
                if has_init == ConDescId::NONE {
                    calc_alg_context
                        .process_context_mut()
                        .node_mut(*process_indi)
                        .set_individual_initialization_concept(concept_descriptor);
                }
            }
            // nondeterministically = hasNondeterministicDependency(dependencyTrackPoint, ctx);
            let nondeterministically =
                self.has_nondeterministic_dependency(dependency_track_point, calc_alg_context);
            // if (conceptDescriptor->getConcept()->getOperatorCode() == CCMARKER)
            //   ctx->getProcessingDataBox()->getMarkerIndividualNodeHash(true)
            //       ->addMarkerIndividualNode(conceptDescriptor->getConcept(), processIndi, nondeterministically);
            if calc_alg_context
                .ontology_arenas()
                .concept(new_concept)
                .get_operator_code()
                == super::super::model::op::CCMARKER
            {
                let marker_hash = calc_alg_context.marker_individual_node_hash(true);
                MarkerIndividualNodeHash::add_marker_individual_node(
                    calc_alg_context.process_context_mut(),
                    marker_hash,
                    new_concept,
                    *process_indi,
                    nondeterministically,
                );
            }
            //
            // if (mConfOccurrenceStatisticsCollecting && mOptCollectOccurrenceStatistics)
            //   mOccStatsCacheHandler->incConceptInstanceOccurrencceStatistics(
            //       conceptDescriptor->getConcept(), nondeterministically, processIndi->getNominalIndividual() == nullptr);
            if self.conf_occurrence_statistics_collecting && self.opt_collect_occurrence_statistics
            {
                let concept_id = calc_alg_context
                    .ontology_arenas()
                    .concept(new_concept)
                    .get_concept_tag();
                let concept_count = calc_alg_context.ontology_arenas().concept_count();
                let role_count = calc_alg_context.ontology_arenas().role_count();
                let deterministic_count = if nondeterministically { 0 } else { 1 };
                let nondeterministic_count = if nondeterministically { 1 } else { 0 };
                let individual_count = if calc_alg_context
                    .process_context()
                    .node(*process_indi)
                    .nominal_individual()
                    .is_some()
                {
                    1
                } else {
                    0
                };
                let existential_count = if individual_count == 0 { 1 } else { 0 };
                calc_alg_context
                    .occurrence_statistics_cache_handler_mut()
                    .inc_concept_instance_occurrencce_statistics(
                        concept_id,
                        concept_count,
                        role_count,
                        deterministic_count,
                        nondeterministic_count,
                        individual_count,
                        existential_count,
                    );
            }
        }

        // if (contained && clashedConceptDescriptor) {
        //   clashConDesLinker = createClashedConceptDescriptor(nullptr, processIndi, clashedConceptDescriptor, clashedDependencyTrackPoint, ctx);
        //   clashConDesLinker = createClashedConceptDescriptor(clashConDesLinker, processIndi, conceptDescriptor, dependencyTrackPoint, ctx);
        //   throw CCalculationClashProcessingException(clashConDesLinker);
        // }
        if contained && clashed_concept_descriptor != ConDescId::NONE {
            // Faithful two-link clash chain (cpp): one `CClashedConceptDescriptor`
            // for the CONTAINED descriptor, one for the NEW one, chained; then the
            // pending-signal stand-in for the throw.
            let mut clash = self.create_clashed_concept_descriptor(
                Id::NONE,
                process_indi,
                clashed_concept_descriptor,
                clashed_dependency_track_point,
                calc_alg_context,
            );
            clash = self.create_clashed_concept_descriptor(
                clash,
                process_indi,
                concept_descriptor,
                dependency_track_point,
                calc_alg_context,
            );
            calc_alg_context.raise_clash(clash);
        }

        // (the large commented-out biotop/amount-of-substance debug block in the C++ is
        //  dead debug code and is intentionally not ported.)
        contained
    }

    // -----------------------------------------------------------------------
    // Port-internal helper: `CConceptDescriptor::initConceptDescriptor`.
    // -----------------------------------------------------------------------

    /// KONCLUDE-PORT-NOTE[api]: `conceptDescriptor->initConceptDescriptor(concept, negate,
    /// depTrackPoint)` (cpp `CConceptDescriptor::initConceptDescriptor` =
    /// `initNegLinker(concept,negated)` + `initDependencyTracker(depTrackPoint)`) is a
    /// W2-deferred `CConceptDescriptor` derived method (descriptor.rs leaves it pending
    /// because the derived form also computes terminology tags). This unit only needs
    /// the field-init effect, so it writes the public descriptor fields directly through
    /// the arena accessor (the same convention u25 uses for wrapper-less node fields).
    pub(super) fn init_concept_descriptor_fields(
        &mut self,
        concept_descriptor: ConDescId,
        concept: ConceptId,
        negate: bool,
        dependency_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // DDB diagnostics: an untracked descriptor poisons every clash
        // analysis it joins (tracking ERROR). Print the first offenders WITH
        // the call path so the untracked creator can be closed.
        if self.conf_build_dependencies
            && dependency_track_point.is_none()
            && self.ddb_analysis_dumps < 3
            && std::env::var_os("KM_BRIDGE_PROGRESS").is_some()
        {
            self.ddb_analysis_dumps += 1;
            let tag = calc_alg_context
                .ontology_arenas()
                .concept(concept)
                .get_concept_tag();
            eprintln!(
                "UNTRACKED-CONDES c={}{} at:\n{}",
                if negate { "¬" } else { "" },
                tag,
                std::backtrace::Backtrace::force_capture()
            );
        }
        let cd = calc_alg_context
            .process_context_mut()
            .con_desc_mut(concept_descriptor);
        cd.concept = concept; // initNegLinker data
        cd.negated = negate; // initNegLinker negation
        cd.next = ConDescId::NONE; // initNegLinker next = nullptr
        cd.dep_track_point = dependency_track_point; // initDependencyTracker
    }
}
