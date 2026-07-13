//! `completion::u10` — Reapply-queue management family (port unit #10 of 36).
//!
//! Faithful port of the 27-method "Reapply-queue management" unit of Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.cpp`
//! (manifest `01-completion-methods.md`, "Unit 10", cpp ranges 6252–27676):
//!
//!   * `reapplySatisfiableCachedAbsorbed{Disjunction,Generating}Concepts`
//!     (6252 / 6275) — flush a node's cached-absorbed reapply linker into its
//!     concept-processing queue,
//!   * the two `reapplyConceptUpdatedRepresentative` overloads (11236 / 11248),
//!   * the `applyReapplyQueueConcepts` family — the propagation-binding linker
//!     (13876), the concept+negation / role / restricted / condensed-iterator
//!     overloads (26523 / 26549 / 26572 / 26602),
//!   * `applyExtendedReapplyConceptDescriptor` (26492, the ATMOST reactivation),
//!   * `collectReapplyAutomatTransactionsRestrictions` (22019, the qualified-∀
//!     automaton restriction collector),
//!   * `createNewIndividualsLink{s,}Reapplyed` (22295 / 22372, link creation that
//!     re-fires the role-keyed reapply queue),
//!   * the five `addConceptToReapplyQueue` overloads (26625..26671) and the two
//!     `isConceptInReapplyQueue` overloads (26674 / 26682).
//!
//! The 7 rule-counter getters that the manifest also lists in this unit
//! (`getAppliedANDRuleCount`..`getAppliedTotalRuleCount`, cpp 27650–27676) are
//! ALREADY ported as inline accessors in `completion/algorithm.rs`
//! (`applied_and_rule_count()`..`applied_total_rule_count()`); they are NOT
//! re-defined here, to avoid a duplicate-method definition on the same impl.
//!
//! KONCLUDE-PORT-NOTE[ownership]: each method is a member of
//! `CCalculationTableauCompletionTaskHandleAlgorithm`, so it becomes `&mut self`
//! plus the threaded per-thread context `calc_alg_context: &mut
//! CalculationAlgorithmContextBase` (the C++ `CCalculationAlgorithmContextBase*`).
//! A `CIndividualProcessNode*` becomes a `NodeId`, a `CConceptDescriptor*` a
//! `ConDescId`, a `CDependencyTrackPoint*` a `TrackPointId`, an
//! `CIndividualLinkEdge*` an `EdgeId`; the static `CConcept*`/`CRole*` become
//! `ConceptId`/`RoleId` (resolved against `ctx.ontology_arenas()`).
//!
//! KONCLUDE-PORT-NOTE[overload]: Rust has no function overloading, so the C++
//! same-name overloads get a disambiguating suffix preserving their distinguishing
//! parameter (`_role` / `_concept` / `_restricted` / `_condensed_iterator` /
//! `_propagation_binding` / `_binding_count`). The original C++ name is kept in
//! each item's doc-comment as the port anchor.
//!
//! KONCLUDE-PORT-NOTE[api]: the reapply machinery hangs off three not-yet-ported
//! subsystems — (1) the per-node intrusive reapply containers and their iterators
//! (`CReapplyQueue` / `CCondensedReapplyQueue` / `CReapplyQueueIterator` /
//! `CCondensedReapplyQueueIterator` / the `CReapplyConceptDescriptor` /
//! `CCondensedReapplyConceptDescriptor` / `CPropagationBindingReapplyConceptDescriptor`
//! linker payloads), reached via node getters (`getConceptProcessingQueue`,
//! `getRoleReapplyQueue`, `getConceptReapplyQueue`, `getRoleReapplyIterator`,
//! `getConceptReapplyIterator`, `getReapplyConceptLabelSet`,
//! `getSatisfiableCachedAbsorbed*Linker`, `getSuccessorIndividualATMOSTReactivationData`)
//! that `process/node.rs` has not yet surfaced; (2) the link-installation helpers
//! (`getLocalizedIndividual`, `hasIndividualsLink`, `installIndividualNodeRoleLinkReapplied`,
//! `createIndividualNodeDisjointRolesLinks`, `addConceptsToIndividual`,
//! `linkCreationDirectlyChangedNeighbourConnectionUpdate`,
//! `setIndividualNodeConceptLabelSetModified`), all siblings in later units; and
//! (3) the per-test memory pool (`getUsedProcessTaskMemoryAllocationManager`) /
//! the STATINC counters. Every such site is transcribed in place and flagged
//! `// W3-DEFER[api]` / `// W3-DEFER[memory-pool]`; control flow is ported in full
//! (loops, polarity XORs, the `if (conProQueue) addIndividualToProcessingQueue`
//! tail), with linker-chain traversals modelled as an (empty until wired) `Vec`
//! and the "was anything queued" sentinel kept as an explicit bool because the
//! `conProQueue` pointer is a stubbed `Id::NONE`. Sibling queue-adders
//! (`addConceptRestrictedToProcessingQueue`, `addConceptToProcessingQueue`,
//! `addConceptPreprocessedToProcessingQueue`, `addIndividualToProcessingQueue`)
//! ARE the ported unit-4 methods and are called for real.

#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_assignments)]
#![allow(unused_mut)]

use std::collections::HashMap;

use super::super::model::op;
use super::super::model::substrate::{Cint64, Id, NegLink, INVALID};
use super::super::model::{ConceptId, RoleId};
use super::super::process::edge::IndividualLinkEdge;
use super::super::process::node::IndividualProcessNode;
use super::super::process::propagation_binding::PropagationBindingReapplyConceptDescriptorId;
use super::super::process::reapply_sat::{
    CondensedReapplyConceptDescriptor, CondensedReapplyQueueIterator, ReapplyConceptDescriptor,
    ReapplyConceptDescriptorId,
};
use super::super::process::rs1::ReapplyQueueIterator;
use super::super::process::satellites::BranchingMergingProcessingRestrictionSpecification;
use super::super::process::stubs::ConceptProcessingQueueId;
use super::super::process::{
    ConDescId, EdgeId, LabelSetId, NodeId, RestrictionSpecId, TrackPointId,
};
use super::super::saturation::satellites::{
    ConceptNegationPair, ReapplyConceptSaturationLabelSetId,
};
use super::context::CalculationAlgorithmContextBase;

/// KONCLUDE-PORT-NOTE[api]: `CProcessingRestrictionSpecification*` is not yet
/// ported; an opaque handle (`INVALID` == `nullptr`), matching `u04`.
type ProcRestrictionHandle = Cint64;
/// KONCLUDE-PORT-NOTE[api]: `CCondensedReapplyQueue*` — not yet ported.
type CondensedReapplyQueueHandle = Cint64;
/// KONCLUDE-PORT-NOTE[api]: `CReapplyQueue*` — not yet ported.
type ReapplyQueueHandle = Cint64;
/// `CCondensedReapplyQueueIterator` (by-value iterator).
type CondensedReapplyQueueIteratorHandle = CondensedReapplyQueueIterator;
/// `CReapplyQueueIterator` (by-value iterator).
type ReapplyQueueIteratorHandle = ReapplyQueueIterator;
/// `CReapplyConceptDescriptor*` linker payload.
type ReapplyConDescHandle = ReapplyConceptDescriptorId;
/// KONCLUDE-PORT-NOTE[api]: `CCondensedReapplyConceptDescriptor*` linker payload.
type CondensedReapplyConDescHandle = Cint64;
/// `CPropagationBindingReapplyConceptDescriptor*` linker.
type PropagationBindingReapplyConDescHandle = PropagationBindingReapplyConceptDescriptorId;
/// KONCLUDE-PORT-NOTE[api]: `CReapplyConceptSaturationLabelSet*` — saturation
/// label-set satellite, not yet ported.
type ReapplyConceptSaturationLabelSetHandle = Cint64;
/// KONCLUDE-PORT-NOTE[api]: `CSortedNegLinker<CRole*>*` — the (inverse-tagged)
/// role linker chain a link-creation iterates; head handle of the chain.
type RoleLinkerHandle = Cint64;

impl super::algorithm::CompletionTaskHandleAlgorithm {
    // =======================================================================
    // W15-rbox: RBox-resolved ∀-propagation targets (role hierarchy + inverse).
    // =======================================================================

    /// Match one physical `edge_role` against the requested role in the given
    /// direction.  Konclude's `createNewIndividualsLinksReapplyed` walks the
    /// edge role's signed indirect-super-role linker: non-negated entries are
    /// installed source-to-destination, negated entries destination-to-source
    /// (cpp 22413–22461).  The sign is therefore semantic, not metadata.
    pub(crate) fn ht_signed_role_matches(
        &self,
        edge_role: RoleId,
        requested_role: RoleId,
        inverse_direction: bool,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> bool {
        if edge_role.is_none() || requested_role.is_none() {
            return false;
        }
        if !inverse_direction && edge_role == requested_role {
            return true;
        }
        let ontology = calc_alg_context.ontology_arenas();
        if ontology
            .role(edge_role)
            .get_indirect_super_role_list()
            .iter()
            .any(|link| link.target == requested_role && link.negated == inverse_direction)
        {
            return true;
        }
        // Hand-built fixtures can wire only `inverse_role`, without running
        // CSubroleTransformationPreProcess to materialize the signed linker.
        inverse_direction && ontology.role(edge_role).get_inverse_role() == requested_role
    }

    /// Collect the role links and nodes an `∀role.C` restriction on `source`
    /// must reach, resolving the RBox on lookup.  Keeping the physical link is
    /// required by Konclude's `applyALLRule` and `applyAutomatTransactions`:
    /// their dependency node combines the restriction's dependency with
    /// `link->getDependencyTrackPoint()`.
    ///
    /// Two RBox dimensions are resolved:
    ///  - **role hierarchy** `R ⊑ S`: a forward edge `source --E--> succ` makes `succ`
    ///    an `S`-successor when `E == S` or `S` is an indirect super-role of `E`
    ///    through a NON-NEGATED `S` entry in `role(E).indirect_super_roles`. So
    ///    `∀S.C` reaches every R-successor with `R ⊑ S`. (Konclude registers a
    ///    distinct edge per indirect super-role on install via
    ///    `createNewIndividualsLinksReapplyed`; the port keeps one forward edge and
    ///    resolves the signed entries here instead.)
    ///  - **inverse roles** `∀R⁻.C`: the predecessor reached through `source`'s ancestor
    ///    link. The ancestor edge is `pred --E--> source`, so `pred` is an `E⁻`-successor
    ///    of `source`; it matches when `role == E⁻` (or `role` is a super-role of `E⁻`).
    ///    (Konclude installs the inverse direction via the negated entries of the
    ///    indirect-super-role list — `installIndividualNodeRoleLink(dst, src, …)`; the
    ///    port reaches the single predecessor via the ancestor link, faithful for the
    ///    blockable-successor regime exercised here.)
    pub fn ht_all_rule_target_links(
        &self,
        source: NodeId,
        role: RoleId,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> Vec<(EdgeId, NodeId)> {
        let mut out: Vec<(EdgeId, NodeId)> = Vec::new();
        let pc = calc_alg_context.process_context();

        // (1) forward successors, hierarchy-resolved.
        let mut it = pc.node_successor_iterator(source);
        while it.has_next() {
            let link: EdgeId = it.next_link(false);
            let succ_id: Cint64 = it.next_individual_id(true);
            if link.is_none() {
                continue;
            }
            let edge_role: RoleId = pc.edge(link).get_link_role();
            let role_matches =
                self.ht_signed_role_matches(edge_role, role, false, calc_alg_context);
            if role_matches {
                let succ = calc_alg_context
                    .processing_data_box()
                    .individual_process_node_vector()
                    .get_data(succ_id);
                if succ.is_some() && !out.iter().any(|&(_, node)| node == succ) {
                    out.push((link, succ));
                }
            }
        }

        // (2) inverse: the predecessor via the ancestor link.
        let anc_link: EdgeId = pc.node(source).get_ancestor_link();
        if anc_link.is_some() {
            let e = pc.edge(anc_link);
            let edge_role: RoleId = e.get_link_role();
            let pred: NodeId = e.get_source_individual();
            if edge_role.is_some() && pred.is_some() {
                let inv_matches =
                    self.ht_signed_role_matches(edge_role, role, true, calc_alg_context);
                if inv_matches && !out.iter().any(|&(_, node)| node == pred) {
                    out.push((anc_link, pred));
                }
            }
        }

        // (2b) inverse: ALL predecessors via the connection-successor set —
        // Konclude registers every link's source there (cpp 22346–22349), so a
        // node with links from several parents (≤n-merge relocation) propagates
        // its ∀R⁻ restrictions to EVERY R-predecessor, not just its creator.
        // (The ancestor arm above keeps hand-built fixtures without conn-sets
        // working; `out.contains` dedups.)
        let conn = pc.node_connection_successor_set_existing(source);
        if conn.is_some() {
            let source_id = pc.node(source).individual_node_id();
            let mut cit = pc.conn_succ_set(conn).get_connection_successor_iterator();
            while cit.has_next() {
                let pred_id = cit.next(true);
                if pred_id == source_id {
                    continue;
                }
                let pred = calc_alg_context
                    .processing_data_box()
                    .individual_process_node_vector()
                    .get_data(pred_id);
                if pred.is_none() || out.iter().any(|&(_, node)| node == pred) {
                    continue;
                }
                let pn = pc.node(pred);
                if pn.has_merged_into_individual_node_id()
                    || pn.has_purged_blocked_processing_restriction_flags()
                {
                    continue;
                }
                let mut lit = pc.node_successor_role_iterator(pred, source_id);
                while lit.has_next() {
                    let link = lit.next(true);
                    if link.is_none() {
                        continue;
                    }
                    let edge_role: RoleId = pc.edge(link).get_link_role();
                    if edge_role.is_none() {
                        continue;
                    }
                    let inv_matches =
                        self.ht_signed_role_matches(edge_role, role, true, calc_alg_context);
                    if inv_matches {
                        out.push((link, pred));
                        break;
                    }
                }
            }
        }
        out
    }

    /// Node-only compatibility view of [`Self::ht_all_rule_target_links`].
    pub fn ht_all_rule_targets(
        &self,
        source: NodeId,
        role: RoleId,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> Vec<NodeId> {
        self.ht_all_rule_target_links(source, role, calc_alg_context)
            .into_iter()
            .map(|(_, node)| node)
            .collect()
    }

    // =======================================================================
    // Satisfiable-cached-absorbed flush (cpp 6252 / 6275).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::reapplySatisfiableCachedAbsorbedDisjunctionConcepts`.
    pub fn reapply_satisfiable_cached_absorbed_disjunction_concepts(
        &mut self,
        individual_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut concepts_reapplyed = false;

        let con_pro_queue = calc_alg_context
            .process_context_mut()
            .node_concept_processing_queue(individual_node, true);
        let mut absorbed_reapply_con_des = calc_alg_context
            .process_context()
            .node(individual_node)
            .satisfiable_cached_absorbed_disjunctions_linker();
        while absorbed_reapply_con_des.is_some() {
            concepts_reapplyed = true;

            let (con_des, dep_track_point, proc_rest, is_static_descriptor, next) = {
                let reapply = calc_alg_context
                    .process_context()
                    .reapply_con_desc(absorbed_reapply_con_des);
                (
                    reapply.get_concept_descriptor(),
                    reapply.get_dependency_track_point(),
                    reapply.get_reapply_processing_restriction(),
                    reapply.is_static_descriptor(),
                    reapply.get_next(),
                )
            };

            self.add_concept_restricted_to_processing_queue(
                con_des,
                dep_track_point,
                con_pro_queue,
                individual_node,
                is_static_descriptor,
                proc_rest,
                calc_alg_context,
            );
            absorbed_reapply_con_des = next;
        }
        calc_alg_context
            .process_context_mut()
            .node_mut(individual_node)
            .clear_satisfiable_cached_absorbed_disjunctions_linker();

        concepts_reapplyed
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::reapplySatisfiableCachedAbsorbedGeneratingConcepts`.
    pub fn reapply_satisfiable_cached_absorbed_generating_concepts(
        &mut self,
        individual_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut concepts_reapplyed = false;

        let con_pro_queue = calc_alg_context
            .process_context_mut()
            .node_concept_processing_queue(individual_node, true);
        let mut absorbed_reapply_con_des = calc_alg_context
            .process_context()
            .node(individual_node)
            .satisfiable_cached_absorbed_generating_linker();
        while absorbed_reapply_con_des.is_some() {
            concepts_reapplyed = true;

            let (con_des, dep_track_point, next) = {
                let reapply = calc_alg_context
                    .process_context()
                    .reapply_con_desc(absorbed_reapply_con_des);
                (
                    reapply.get_concept_descriptor(),
                    reapply.get_dependency_track_point(),
                    reapply.get_next(),
                )
            };

            self.add_concept_to_processing_queue(
                con_des,
                dep_track_point,
                con_pro_queue,
                individual_node,
                false,
                calc_alg_context,
            );
            absorbed_reapply_con_des = next;
        }
        calc_alg_context
            .process_context_mut()
            .node_mut(individual_node)
            .clear_satisfiable_cached_absorbed_generating_linker();

        concepts_reapplyed
    }

    // =======================================================================
    // reapplyConceptUpdatedRepresentative — representative re-fire (cpp 11236 / 11248).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::reapplyConceptUpdatedRepresentative`
    /// (the `CReapplyConceptLabelSet*`/no-binding-count overload).
    pub fn reapply_concept_updated_representative(
        &mut self,
        process_indi: NodeId,
        binding_con_des: ConDescId,
        binding_dep_track_point: TrackPointId,
        mut con_set: LabelSetId,
        reapply_queue: CondensedReapplyQueueHandle,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[api]: setIndividualNodeConceptLabelSetModified(processIndi,calcAlgContext); — helper, later unit.
        let con_pro_queue: ConceptProcessingQueueId = calc_alg_context
            .process_context_mut()
            .node_concept_processing_queue(process_indi, true);
        // addConceptPreprocessedToProcessingQueue(bindingConDes,bindingDepTrackPoint,conProQueue,processIndi,true,calcAlgContext);
        // (the `allowPreprocessing` overload — skipFunction defaults to nullptr == INVALID).
        self.add_concept_preprocessed_to_processing_queue_skip(
            binding_con_des,
            binding_dep_track_point,
            con_pro_queue,
            process_indi,
            true,
            calc_alg_context,
            INVALID,
        );
        // W3-DEFER[api]: reapplyQueue->isEmpty()
        let reapply_queue_empty = true;
        let _ = reapply_queue;
        if !reapply_queue_empty {
            // W3-DEFER[api]: conSet = processIndi->getReapplyConceptLabelSet(true);
            con_set = Id::NONE;
            // W3-DEFER[api]: CCondensedReapplyQueueIterator reapplyQueueIt(conSet->getConceptReapplyIterator(bindingConDes));
            let reapply_queue_it = CondensedReapplyQueueIterator::new();
            self.apply_reapply_queue_concepts_condensed_iterator(
                process_indi,
                reapply_queue_it,
                calc_alg_context,
            );
            let _ = con_set;
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::reapplyConceptUpdatedRepresentative`
    /// (the `bindingCount` overload).
    pub fn reapply_concept_updated_representative_binding_count(
        &mut self,
        process_indi: NodeId,
        binding_con_des: ConDescId,
        binding_dep_track_point: TrackPointId,
        binding_count: Cint64,
        mut con_set: LabelSetId,
        reapply_queue: CondensedReapplyQueueHandle,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[api]: setIndividualNodeConceptLabelSetModified(processIndi,calcAlgContext);
        let con_pro_queue: ConceptProcessingQueueId = calc_alg_context
            .process_context_mut()
            .node_concept_processing_queue(process_indi, true);
        // addConceptPreprocessedToProcessingQueue(bindingConDes,bindingDepTrackPoint,conProQueue,processIndi,bindingCount,calcAlgContext);
        self.add_concept_preprocessed_to_processing_queue(
            binding_con_des,
            binding_dep_track_point,
            con_pro_queue,
            process_indi,
            binding_count,
            calc_alg_context,
        );
        // W3-DEFER[api]: reapplyQueue->isEmpty()
        let reapply_queue_empty = true;
        let _ = reapply_queue;
        if !reapply_queue_empty {
            // W3-DEFER[api]: conSet = processIndi->getReapplyConceptLabelSet(true);
            con_set = Id::NONE;
            // W3-DEFER[api]: CCondensedReapplyQueueIterator reapplyQueueIt(conSet->getConceptReapplyIterator(bindingConDes));
            let reapply_queue_it = CondensedReapplyQueueIterator::new();
            self.apply_reapply_queue_concepts_condensed_iterator(
                process_indi,
                reapply_queue_it,
                calc_alg_context,
            );
            let _ = con_set;
        }
    }

    // =======================================================================
    // applyReapplyQueueConcepts family (cpp 13876 / 26523 / 26549 / 26572 / 26602).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyReapplyQueueConcepts`
    /// (the `CPropagationBindingReapplyConceptDescriptor*` linker overload, cpp 13876).
    pub fn apply_reapply_queue_concepts_propagation_binding(
        &mut self,
        process_indi: NodeId,
        reapply_des_linker: PropagationBindingReapplyConDescHandle,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // process_indi node id (real accessor) is the localisation discriminator below.
        let process_indi_id = calc_alg_context
            .process_context()
            .node(process_indi)
            .individual_node_id();
        let mut reapply_des_linker_it = reapply_des_linker;
        while reapply_des_linker_it.is_some() {
            // W3-DEFER[api]: STATINC(PBINDREAPPLICATIONCOUNT,calcAlgContext);
            let (con_des, indi_node, next_reapply_des) = {
                let reapply_des_ref = calc_alg_context
                    .process_context()
                    .prop_binding_reapply_con_des(reapply_des_linker_it);
                (
                    reapply_des_ref.get_concept_descriptor(),
                    reapply_des_ref.get_reapply_individual_node(),
                    reapply_des_ref.get_next(),
                )
            };
            let dep_track_point = calc_alg_context
                .process_context()
                .con_desc(con_des)
                .get_dependency_track_point();
            let mut loc_indi_node = indi_node;

            let indi_node_id = calc_alg_context
                .process_context()
                .node(indi_node)
                .individual_node_id();
            if process_indi_id != indi_node_id {
                // locIndiNode = getLocalizedIndividual(indiNode,true,calcAlgContext);
                loc_indi_node = self.get_localized_individual(indi_node, true, calc_alg_context);
            }

            let con_pro_queue = calc_alg_context
                .process_context_mut()
                .node_concept_processing_queue(loc_indi_node, true);
            self.add_concept_restricted_to_processing_queue(
                con_des,
                dep_track_point,
                con_pro_queue,
                loc_indi_node,
                false,
                INVALID,
                calc_alg_context,
            );

            if process_indi_id != indi_node_id {
                self.add_individual_to_processing_queue(loc_indi_node, calc_alg_context);
            }
            reapply_des_linker_it = next_reapply_des;
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyReapplyQueueConcepts`
    /// (the `CConcept*` + `negation` overload, cpp 26523).
    pub fn apply_reapply_queue_concepts_concept(
        &mut self,
        process_indi: NodeId,
        concept: ConceptId,
        negation: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[memory-pool]: taskMemMan = calcAlgContext->getUsedProcessTaskMemoryAllocationManager();
        let concept_tag = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_concept_tag();
        let mut reapply_queue_it = calc_alg_context
            .process_context_mut()
            .node_concept_reapply_iterator_by_tag(process_indi, concept_tag, negation, true);
        let mut con_pro_queue: ConceptProcessingQueueId = Id::NONE;
        let mut con_pro_queue_set = false;
        while reapply_queue_it.has_next() {
            let reapply_concept_des =
                reapply_queue_it.next(calc_alg_context.process_context(), true);
            if reapply_concept_des.is_none() {
                continue;
            }
            // W3-DEFER[api]: STATINC(REAPPLIEDCONCEPTSCOUNT,calcAlgContext);
            let (con_des, dep_track_point, proc_rest, is_static_descriptor, is_extended) = {
                let reapply_concept_des_ref = calc_alg_context
                    .process_context()
                    .cond_reapply_con_desc(reapply_concept_des);
                (
                    reapply_concept_des_ref.get_concept_descriptor(),
                    reapply_concept_des_ref.get_dependency_track_point(),
                    reapply_concept_des_ref.get_reapply_processing_restriction(),
                    reapply_concept_des_ref.is_static_descriptor(),
                    reapply_concept_des_ref.is_extended(),
                )
            };
            if is_extended {
                // W3-DEFER[api]: extended condensed descriptors are ATMOST
                // reactivation records; the extension payload is not ported yet.
                let _ = (process_indi, concept, negation, reapply_concept_des);
            } else {
                if !con_pro_queue_set {
                    con_pro_queue = calc_alg_context
                        .process_context_mut()
                        .node_concept_processing_queue(process_indi, true);
                    con_pro_queue_set = true;
                }
                self.add_concept_restricted_to_processing_queue(
                    con_des,
                    dep_track_point,
                    con_pro_queue,
                    process_indi,
                    is_static_descriptor,
                    proc_rest,
                    calc_alg_context,
                );
            }
        }
        if con_pro_queue_set {
            self.add_individual_to_processing_queue(process_indi, calc_alg_context);
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyReapplyQueueConcepts`
    /// (the `CRole*` overload, cpp 26549).
    pub fn apply_reapply_queue_concepts_role(
        &mut self,
        process_indi: NodeId,
        role: RoleId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[memory-pool]: taskMemMan = calcAlgContext->getUsedProcessTaskMemoryAllocationManager();
        let mut reapply_queue_it = calc_alg_context
            .process_context_mut()
            .node_role_reapply_iterator(process_indi, role, true);
        let mut con_pro_queue: ConceptProcessingQueueId = Id::NONE;
        let mut con_pro_queue_set = false;
        while reapply_queue_it.has_next() {
            let reapply_concept_des =
                reapply_queue_it.next(calc_alg_context.process_context(), true);
            if reapply_concept_des.is_none() {
                continue;
            }
            // W3-DEFER[api]: STATINC(REAPPLIEDCONCEPTSCOUNT,calcAlgContext);
            let (con_des, dep_track_point, proc_rest, is_static_descriptor) = {
                let reapply_concept_des_ref = calc_alg_context
                    .process_context()
                    .reapply_con_desc(reapply_concept_des);
                (
                    reapply_concept_des_ref.get_concept_descriptor(),
                    reapply_concept_des_ref.get_dependency_track_point(),
                    reapply_concept_des_ref.get_reapply_processing_restriction(),
                    reapply_concept_des_ref.is_static_descriptor(),
                )
            };
            if !con_pro_queue_set {
                con_pro_queue = calc_alg_context
                    .process_context_mut()
                    .node_concept_processing_queue(process_indi, true);
                con_pro_queue_set = true;
            }
            self.add_concept_restricted_to_processing_queue(
                con_des,
                dep_track_point,
                con_pro_queue,
                process_indi,
                is_static_descriptor,
                proc_rest,
                calc_alg_context,
            );
        }
        if con_pro_queue_set {
            self.add_individual_to_processing_queue(process_indi, calc_alg_context);
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyReapplyQueueConceptsRestricted`
    /// (the `CReapplyQueueIterator*` + `restrictedLink` overload, cpp 26572).
    pub fn apply_reapply_queue_concepts_restricted(
        &mut self,
        process_indi: NodeId,
        mut reapply_queue_it: ReapplyQueueIteratorHandle,
        restricted_link: EdgeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[memory-pool]: taskMemMan = calcAlgContext->getUsedProcessTaskMemoryAllocationManager();
        let mut con_pro_queue: ConceptProcessingQueueId = Id::NONE;
        let mut con_pro_queue_set = false;
        // CLinkProcessingRestrictionSpecification* linkProcRest = nullptr;
        let mut link_proc_rest: ProcRestrictionHandle = INVALID;
        while reapply_queue_it.has_next() {
            // W3-DEFER[api]: STATINC(REAPPLIEDCONCEPTSCOUNT,calcAlgContext);
            let reapply_concept_des =
                reapply_queue_it.next(calc_alg_context.process_context(), true);
            if reapply_concept_des.is_none() {
                continue;
            }
            let (con_des, dep_track_point, mut proc_rest, is_static_descriptor) = {
                let reapply_concept_des_ref = calc_alg_context
                    .process_context()
                    .reapply_con_desc(reapply_concept_des);
                (
                    reapply_concept_des_ref.get_concept_descriptor(),
                    reapply_concept_des_ref.get_dependency_track_point(),
                    reapply_concept_des_ref.get_reapply_processing_restriction(),
                    reapply_concept_des_ref.is_static_descriptor(),
                )
            };
            if !con_pro_queue_set {
                con_pro_queue = calc_alg_context
                    .process_context_mut()
                    .node_concept_processing_queue(process_indi, true);
                con_pro_queue_set = true;
            }
            // KM_BRIDGE_SEARCH_LOG: every role-reapply re-fire — the stale-≤n
            // hunt (a reapplied concept must still be IN the node's label).
            if std::env::var_os("KM_BRIDGE_SEARCH_LOG").is_some() {
                let pc = calc_alg_context.process_context();
                let cd = pc.con_desc(con_des);
                let tag = calc_alg_context
                    .ontology_arenas()
                    .concept(cd.get_concept())
                    .get_concept_tag();
                let neg = cd.is_negated();
                let ls = pc.node(process_indi).use_reapply_con_label_set;
                let (tag_present, desc_same) = if ls.is_some() {
                    match pc.label_set(ls).concept_des_dep_map.get(&tag) {
                        Some(d) if !d.concept_descriptor.is_none() => {
                            let same_pol = pc.con_desc(d.concept_descriptor).is_negated() == neg;
                            (same_pol, d.concept_descriptor == con_des)
                        }
                        _ => (false, false),
                    }
                } else {
                    (false, false)
                };
                let opc = calc_alg_context
                    .ontology_arenas()
                    .concept(cd.get_concept())
                    .get_operator_code();
                let m = format!(
                    "reapply-fire node={} tag={}{} op={:?} static={} tag_present={} desc_same={} depth={}",
                    process_indi.index(),
                    if neg { "-" } else { "" },
                    tag,
                    opc,
                    is_static_descriptor,
                    tag_present,
                    desc_same,
                    pc.branch_epoch_depth()
                );
                self.ht_search_log(&m);
            }
            if proc_rest == INVALID {
                if link_proc_rest == INVALID {
                    let mut link_rest =
                        BranchingMergingProcessingRestrictionSpecification::new(INVALID);
                    link_rest.init_link_restriction(restricted_link);
                    link_proc_rest = calc_alg_context
                        .process_context_mut()
                        .alloc_restriction_spec(link_rest)
                        .raw;
                }
                proc_rest = link_proc_rest;
            }
            self.add_concept_restricted_to_processing_queue(
                con_des,
                dep_track_point,
                con_pro_queue,
                process_indi,
                is_static_descriptor,
                proc_rest,
                calc_alg_context,
            );
        }
        if con_pro_queue_set {
            self.add_individual_to_processing_queue(process_indi, calc_alg_context);
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyReapplyQueueConcepts`
    /// (the `CCondensedReapplyQueueIterator*` overload, cpp 26602).
    pub fn apply_reapply_queue_concepts_condensed_iterator(
        &mut self,
        process_indi: NodeId,
        mut reapply_queue_it: CondensedReapplyQueueIteratorHandle,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[memory-pool]: taskMemMan = calcAlgContext->getUsedProcessTaskMemoryAllocationManager();
        let mut con_pro_queue: ConceptProcessingQueueId = Id::NONE;
        let mut con_pro_queue_set = false;
        while reapply_queue_it.has_next() {
            // W3-DEFER[api]: STATINC(REAPPLIEDCONCEPTSCOUNT,calcAlgContext);
            let reapply_concept_des =
                reapply_queue_it.next(calc_alg_context.process_context(), true);
            if reapply_concept_des.is_none() {
                continue;
            }
            let (con_des, dep_track_point, proc_rest, is_static_descriptor, extended) = {
                let reapply_concept_des_ref = calc_alg_context
                    .process_context()
                    .cond_reapply_con_desc(reapply_concept_des);
                (
                    reapply_concept_des_ref.get_concept_descriptor(),
                    reapply_concept_des_ref.get_dependency_track_point(),
                    reapply_concept_des_ref.get_reapply_processing_restriction(),
                    reapply_concept_des_ref.is_static_descriptor(),
                    reapply_concept_des_ref.extended,
                )
            };
            if extended {
                // `applyExtendedReapplyConceptDescriptor` (cpp 26492), ATMOST
                // reactivation: a missing qualifier operand just landed on
                // THIS node (an at-most candidate that was undecided when the
                // ≤n fired). Hand the candidate back to the rest's
                // both-qualify list — the resumed spine re-classifies it —
                // and re-queue the ≤n on the counted parent.
                let (parent, link) = {
                    let d = calc_alg_context
                        .process_context()
                        .cond_reapply_con_desc(reapply_concept_des);
                    (d.atmost_reactivation_node, d.atmost_reactivation_link)
                };
                let parent_dead = {
                    let n = calc_alg_context.process_context().node(parent);
                    n.has_merged_into_individual_node_id()
                        || n.has_purged_blocked_processing_restriction_flags()
                };
                if !parent_dead {
                    if proc_rest != INVALID {
                        let rest_id = RestrictionSpecId::new(proc_rest);
                        let linker = {
                            let mut l = super::super::process::stubs::BranchingMergingIndividualNodeCandidateLinker::new();
                            l.init_branching_merging_individual_node_candidate(process_indi, link);
                            calc_alg_context
                                .process_context_mut()
                                .alloc_branching_merging_candidate_linker(l)
                        };
                        self.ht_with_atmost_rest(rest_id, calc_alg_context, |_alg, rest, ctx| {
                            rest.add_both_qualify_candidate_node_linker(
                                linker,
                                ctx.process_context_mut(),
                            );
                        });
                    }
                    let parent_queue = calc_alg_context
                        .process_context_mut()
                        .node_concept_processing_queue(parent, true);
                    self.add_concept_restricted_to_processing_queue(
                        con_des,
                        dep_track_point,
                        parent_queue,
                        parent,
                        true,
                        proc_rest,
                        calc_alg_context,
                    );
                    self.add_individual_to_processing_queue(parent, calc_alg_context);
                }
                continue;
            }
            if !con_pro_queue_set {
                con_pro_queue = calc_alg_context
                    .process_context_mut()
                    .node_concept_processing_queue(process_indi, true);
                con_pro_queue_set = true;
            }
            self.add_concept_restricted_to_processing_queue(
                con_des,
                dep_track_point,
                con_pro_queue,
                process_indi,
                is_static_descriptor,
                proc_rest,
                calc_alg_context,
            );
        }
        if con_pro_queue_set {
            self.add_individual_to_processing_queue(process_indi, calc_alg_context);
        }
    }

    // =======================================================================
    // applyExtendedReapplyConceptDescriptor — ATMOST reactivation (cpp 26492).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyExtendedReapplyConceptDescriptor`.
    pub fn apply_extended_reapply_concept_descriptor(
        &mut self,
        process_indi: NodeId,
        concept: ConceptId,
        negation: bool,
        reapply_concept_des: CondensedReapplyConDescHandle,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let _ = (process_indi, concept, negation, reapply_concept_des);
        // CExtendedCondensedReapplyConceptDescriptor* extendedReapplyConceptDes = (cast)reapplyConceptDes;
        // W3-DEFER[api]: extendedReapplyConceptDes->getExtentionType() == REAPPLYCONCEPTDESCRIPTOREXTENSIONTYPEATMOST
        let extention_type_is_atmost = false;
        if extention_type_is_atmost {
            // CExtendedCondensedReapplyConceptDescriptorATMOSTReactivation* atmostReapplyConDes = (cast)extendedReapplyConceptDes;
            // W3-DEFER[api]: reapplicationIndiNode = atmostReapplyConDes->getReapplicationIndividualNode();
            let reapplication_indi_node: NodeId = Id::NONE;
            // W3-DEFER[api]: indiLinkEdge = atmostReapplyConDes->getIndividualLink();
            let indi_link_edge: EdgeId = Id::NONE;
            // locReapplicationIndiNode = getLocalizedIndividual(reapplicationIndiNode,true,calcAlgContext);
            let loc_reapplication_indi_node: NodeId =
                self.get_localized_individual(reapplication_indi_node, true, calc_alg_context);

            // W3-DEFER[api]: !locReapplicationIndiNode->hasProcessingRestrictionFlags(PRFPURGEDBLOCKED)
            let _ = IndividualProcessNode::PRF_PURGEDBLOCKED;
            let has_purged_blocked = false;
            if !has_purged_blocked {
                // W3-DEFER[api]: succIndiATMOSTReactivationData = locReapplicationIndiNode->getSuccessorIndividualATMOSTReactivationData(true);
                // W3-DEFER[api]: atmostConDes = atmostReapplyConDes->getConceptDescriptor();
                let atmost_con_des: ConDescId = Id::NONE;
                // W3-DEFER[api]: succIndiATMOSTReactivationData->addReactivationSuccessorIndividualLink(atmostConDes,indiLinkEdge);
                let _ = indi_link_edge;

                // W3-DEFER[api]: role = atmostConDes->getConcept()->getRole();
                let role: RoleId = Id::NONE;
                // W3-DEFER[api]: roleReapplyQueueIt = locReapplicationIndiNode->getRoleReapplyIterator(role,false);
                let role_reapply_queue_chain: Vec<ReapplyConDescHandle> = Vec::new();
                let mut role_queue_reapplied = false;
                let mut role_reapply_iter = role_reapply_queue_chain.into_iter();
                while !role_queue_reapplied {
                    let role_reapply_concept_des = match role_reapply_iter.next() {
                        Some(v) => v,
                        None => break,
                    };
                    // W3-DEFER[api]: roleReapplyConceptDes->getConceptDescriptor() == atmostConDes
                    let role_reapply_con_des: ConDescId = Id::NONE;
                    if role_reapply_con_des == atmost_con_des {
                        self.apply_reapply_queue_concepts_role(
                            loc_reapplication_indi_node,
                            role,
                            calc_alg_context,
                        );
                        role_queue_reapplied = true;
                    }
                    let _ = role_reapply_concept_des;
                }
            }
        }
    }

    // =======================================================================
    // collectReapplyAutomatTransactionsRestrictions — qualified-∀ automaton
    // restriction collector (cpp 22019). Ported against the real ontology arenas.
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::collectReapplyAutomatTransactionsRestrictions`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: the C++ `CPROCESSINGHASH<cint64,
    /// CConceptNegationPair>*& conExtensionMap` is a pointer-reference allocated on
    /// first use (`if (!conExtensionMap) conExtensionMap = …`); ported as a
    /// `&mut Option<HashMap<…>>` so the lazy "allocate if null then insert"
    /// semantics survive (`get_or_insert_with(HashMap::new)`).
    pub fn collect_reapply_automat_transactions_restrictions(
        &mut self,
        process_indi: NodeId,
        collecting_role: RoleId,
        concept: ConceptId,
        negated: bool,
        con_extension_map: &mut Option<HashMap<Cint64, ConceptNegationPair>>,
        con_set: ReapplyConceptSaturationLabelSetHandle,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // cint64 opCode = concept->getOperatorCode();
        let _op_code = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operator_code();
        let concept_operator = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_concept_operator();
        let has_aqand = concept_operator.has_partial_operator_code_flag(op::CCFS_AQAND_TYPE);
        let has_all_aqall =
            concept_operator.has_partial_operator_code_flag(op::CCFS_ALL_AQALL_TYPE);
        let has_some = concept_operator.has_partial_operator_code_flag(op::CCFS_SOME_TYPE);

        if self.conf_specialized_automate_rules && !negated && has_aqand {
            // recurse over operands
            let op_concepts: Vec<NegLink<ConceptId>> = calc_alg_context
                .ontology_arenas()
                .concept(concept)
                .get_operand_list()
                .to_vec();
            for op_concept in op_concepts {
                self.collect_reapply_automat_transactions_restrictions(
                    process_indi,
                    collecting_role,
                    op_concept.target,
                    op_concept.negated,
                    con_extension_map,
                    con_set,
                    calc_alg_context,
                );
            }
        } else if (!negated && has_all_aqall) || (negated && has_some) {
            // CRole* role = concept->getRole();
            let role = calc_alg_context
                .ontology_arenas()
                .concept(concept)
                .get_role();
            if role == collecting_role {
                if (!negated && has_all_aqall) || (negated && has_some) {
                    let rea_op_concepts: Vec<NegLink<ConceptId>> = calc_alg_context
                        .ontology_arenas()
                        .concept(concept)
                        .get_operand_list()
                        .to_vec();
                    for rea_op_concept in rea_op_concepts {
                        let rea_op_con_negation = rea_op_concept.negated ^ negated;

                        let con_set_id = ReapplyConceptSaturationLabelSetId::new(con_set);
                        let con_set_contains_concept = if con_set_id.is_some() {
                            super::super::saturation::algorithm::SaturationTaskHandleAlgorithm::sat_label_set_contains_concept_get_negation(
                                con_set_id,
                                rea_op_concept.target,
                                calc_alg_context,
                            ) == Some(rea_op_con_negation)
                        } else {
                            false
                        };
                        if con_set == INVALID || !con_set_contains_concept {
                            // W3-DEFER[api]: STATINC(NODESUCCESSOREXPANSIONSATURATIONRESOLVINGCONCEPTCANDIDATECOUNT,calcAlgContext);
                            // conExtensionMap->insert(reaOp->getConceptTag(), CConceptNegationPair(reaOp, reaOpConNegation));
                            let con_tag = calc_alg_context
                                .ontology_arenas()
                                .concept(rea_op_concept.target)
                                .get_concept_tag();
                            con_extension_map.get_or_insert_with(HashMap::new).insert(
                                con_tag,
                                ConceptNegationPair::new(
                                    rea_op_concept.target,
                                    rea_op_con_negation,
                                ),
                            );
                        }
                    }
                }
            }
        }
        let _ = process_indi;
    }

    // =======================================================================
    // createNewIndividualsLink{s,}Reapplyed — link creation that re-fires the
    // role-keyed reapply queue (cpp 22295 / 22372).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::createNewIndividualsLinksReapplyed`
    /// (the `CSortedNegLinker<CRole*>*` multi-role overload, cpp 22295).
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: `indiSource`/`indiDestination` are C++
    /// `CIndividualProcessNode*&` (not reassigned here) → `NodeId`. Returns the
    /// created edge for `ancRole` (or `Id::NONE` == `nullptr`).
    pub fn create_new_individuals_links_reapplyed(
        &mut self,
        indi_source: NodeId,
        indi_destination: NodeId,
        role_linker_it: &[NegLink<RoleId>],
        anc_role: RoleId,
        dep_track_point: TrackPointId,
        check_role_existing: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> EdgeId {
        let mut anc_role_link: EdgeId = Id::NONE;
        // W3-DEFER[memory-pool]: taskMemMan = calcAlgContext->getUsedProcessTaskMemoryAllocationManager();
        let mut generated_inv_link = false;

        let role_chain: Vec<NegLink<RoleId>> = role_linker_it.to_vec();
        for role_link in role_chain {
            let role = role_link.target;
            let inv_role = role_link.negated;
            let range_con_linker_it = calc_alg_context
                .ontology_arenas()
                .role(role)
                .get_range_concept_list()
                .to_vec();
            let domain_con_linker_it = calc_alg_context
                .ontology_arenas()
                .role(role)
                .get_domain_concept_list()
                .to_vec();
            let disjoint_role_linker = calc_alg_context
                .ontology_arenas()
                .role(role)
                .get_disjoint_role_list()
                .to_vec();
            // W3-DEFER[api]: STATINC(LINKSCREATIONCOUNT,calcAlgContext);
            // W3-DEFER[memory-pool]: individualLink = allocateAndConstructAndParameterize(taskMemMan, getUsedProcessContext());
            let mut individual_link: EdgeId = Id::NONE;
            if !inv_role {
                let mut source_ref = indi_source;
                let mut destination_ref = indi_destination;
                let has_individuals_link = self.get_individual_node_link(
                    &mut source_ref,
                    &mut destination_ref,
                    role,
                    calc_alg_context,
                ) != Id::NONE;
                if !check_role_existing || !has_individuals_link {
                    let mut source_ref = indi_source;
                    let mut destination_ref = indi_destination;
                    self.create_individual_node_disjoint_roles_links(
                        &mut source_ref,
                        &mut destination_ref,
                        &disjoint_role_linker,
                        dep_track_point,
                        calc_alg_context,
                    );
                    let mut edge = IndividualLinkEdge::new();
                    edge.creator = indi_source;
                    edge.set_source_individual(indi_source);
                    edge.set_destination_individual(indi_destination);
                    edge.set_link_role(role);
                    edge.set_dependency_track_point(dep_track_point);
                    individual_link = calc_alg_context.process_context_mut().alloc_edge(edge);
                    let mut source_ref = indi_source;
                    let mut destination_ref = indi_destination;
                    let reapply_iterator = self.install_individual_node_role_link_reapplied(
                        &mut source_ref,
                        &mut destination_ref,
                        individual_link,
                        calc_alg_context,
                    );
                    if !range_con_linker_it.is_empty() {
                        let mut destination_ref = indi_destination;
                        self.add_concepts_to_individual(
                            &range_con_linker_it,
                            false,
                            &mut destination_ref,
                            dep_track_point,
                            true,
                            false,
                            None,
                            calc_alg_context,
                        );
                    }
                    if !domain_con_linker_it.is_empty() {
                        let mut source_ref = indi_source;
                        self.add_concepts_to_individual(
                            &domain_con_linker_it,
                            false,
                            &mut source_ref,
                            dep_track_point,
                            true,
                            false,
                            None,
                            calc_alg_context,
                        );
                    }
                    self.apply_reapply_queue_concepts_restricted(
                        indi_source,
                        reapply_iterator,
                        individual_link,
                        calc_alg_context,
                    );
                }
            } else {
                let mut source_ref = indi_destination;
                let mut destination_ref = indi_source;
                let has_individuals_link = self.get_individual_node_link(
                    &mut source_ref,
                    &mut destination_ref,
                    role,
                    calc_alg_context,
                ) != Id::NONE;
                if !check_role_existing || !has_individuals_link {
                    generated_inv_link = true;
                    let mut source_ref = indi_destination;
                    let mut destination_ref = indi_source;
                    self.create_individual_node_disjoint_roles_links(
                        &mut source_ref,
                        &mut destination_ref,
                        &disjoint_role_linker,
                        dep_track_point,
                        calc_alg_context,
                    );
                    let mut edge = IndividualLinkEdge::new();
                    edge.creator = indi_source;
                    edge.set_source_individual(indi_destination);
                    edge.set_destination_individual(indi_source);
                    edge.set_link_role(role);
                    edge.set_dependency_track_point(dep_track_point);
                    individual_link = calc_alg_context.process_context_mut().alloc_edge(edge);
                    let mut source_ref = indi_destination;
                    let mut destination_ref = indi_source;
                    let reapply_iterator = self.install_individual_node_role_link_reapplied(
                        &mut source_ref,
                        &mut destination_ref,
                        individual_link,
                        calc_alg_context,
                    );
                    if !range_con_linker_it.is_empty() {
                        let mut destination_ref = indi_source;
                        self.add_concepts_to_individual(
                            &range_con_linker_it,
                            false,
                            &mut destination_ref,
                            dep_track_point,
                            true,
                            false,
                            None,
                            calc_alg_context,
                        );
                    }
                    if !domain_con_linker_it.is_empty() {
                        let mut source_ref = indi_destination;
                        self.add_concepts_to_individual(
                            &domain_con_linker_it,
                            false,
                            &mut source_ref,
                            dep_track_point,
                            true,
                            false,
                            None,
                            calc_alg_context,
                        );
                    }
                    self.apply_reapply_queue_concepts_restricted(
                        indi_destination,
                        reapply_iterator,
                        individual_link,
                        calc_alg_context,
                    );
                }
            }
            if anc_role == role {
                anc_role_link = individual_link;
            }
        }

        // indiDestination->isNominalIndividualNode() — real accessor.
        let indi_destination_is_nominal = calc_alg_context
            .process_context()
            .node(indi_destination)
            .is_nominal_individual_node();
        // Individual-node ids for the connection-successor inserts (read before the
        // &mut process-context borrow of the lazy connection-successor-set getter).
        let indi_source_id = calc_alg_context
            .process_context()
            .node(indi_source)
            .individual_node_id();
        let indi_destination_id = calc_alg_context
            .process_context()
            .node(indi_destination)
            .individual_node_id();
        if generated_inv_link || indi_destination_is_nominal {
            // indiSource->getConnectionSuccessorSet(true)->insertConnectionSuccessor(indiDestination->getIndividualNodeID());
            let conn_succ_set = calc_alg_context
                .process_context_mut()
                .node_connection_successor_set(indi_source);
            calc_alg_context
                .process_context_mut()
                .conn_succ_set_mut(conn_succ_set)
                .insert_connection_successor(indi_destination_id);
        }
        // indiDestination->getConnectionSuccessorSet(true)->insertConnectionSuccessor(indiSource->getIndividualNodeID());
        let conn_succ_set = calc_alg_context
            .process_context_mut()
            .node_connection_successor_set(indi_destination);
        calc_alg_context
            .process_context_mut()
            .conn_succ_set_mut(conn_succ_set)
            .insert_connection_successor(indi_source_id);
        if self.opt_incremental_compatible_expansion {
            // W3-DEFER[api]: linkCreationDirectlyChangedNeighbourConnectionUpdate(indiDestination,indiSource,true,calcAlgContext);
        }
        anc_role_link
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::createNewIndividualsLinkReapplyed`
    /// (the single-`CRole*` overload, cpp 22372).
    pub fn create_new_individuals_link_reapplyed(
        &mut self,
        indi_creator: NodeId,
        indi_source: NodeId,
        indi_destination: NodeId,
        role: RoleId,
        dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> EdgeId {
        // W3-DEFER[memory-pool]: taskMemMan = calcAlgContext->getUsedProcessTaskMemoryAllocationManager();
        let disjoint_role_linker = calc_alg_context
            .ontology_arenas()
            .role(role)
            .get_disjoint_role_list()
            .to_vec();
        let mut source_ref = indi_source;
        let mut destination_ref = indi_destination;
        self.create_individual_node_disjoint_roles_links(
            &mut source_ref,
            &mut destination_ref,
            &disjoint_role_linker,
            dep_track_point,
            calc_alg_context,
        );
        // W3-DEFER[api]: STATINC(LINKSCREATIONCOUNT,calcAlgContext);
        // W3-DEFER[memory-pool]: individualLink = allocateAndConstructAndParameterize(taskMemMan, getUsedProcessContext());
        let mut edge = IndividualLinkEdge::new();
        edge.creator = indi_creator;
        edge.set_source_individual(indi_source);
        edge.set_destination_individual(indi_destination);
        edge.set_link_role(role);
        edge.set_dependency_track_point(dep_track_point);
        let individual_link: EdgeId = calc_alg_context.process_context_mut().alloc_edge(edge);
        let mut source_ref = indi_source;
        let mut destination_ref = indi_destination;
        let reapply_iterator = self.install_individual_node_role_link_reapplied(
            &mut source_ref,
            &mut destination_ref,
            individual_link,
            calc_alg_context,
        );
        let range_con_linker_it = calc_alg_context
            .ontology_arenas()
            .role(role)
            .get_range_concept_list()
            .to_vec();
        if !range_con_linker_it.is_empty() {
            let mut destination_ref = indi_destination;
            self.add_concepts_to_individual(
                &range_con_linker_it,
                false,
                &mut destination_ref,
                dep_track_point,
                false,
                false,
                None,
                calc_alg_context,
            );
        }
        let domain_con_linker_it = calc_alg_context
            .ontology_arenas()
            .role(role)
            .get_domain_concept_list()
            .to_vec();
        if !domain_con_linker_it.is_empty() {
            let mut source_ref = indi_source;
            self.add_concepts_to_individual(
                &domain_con_linker_it,
                false,
                &mut source_ref,
                dep_track_point,
                false,
                false,
                None,
                calc_alg_context,
            );
        }
        self.apply_reapply_queue_concepts_restricted(
            indi_source,
            reapply_iterator,
            individual_link,
            calc_alg_context,
        );
        // indiDestination->getConnectionSuccessorSet(true)->insertConnectionSuccessor(indiSource->getIndividualNodeID());
        let indi_source_id = calc_alg_context
            .process_context()
            .node(indi_source)
            .individual_node_id();
        let conn_succ_set = calc_alg_context
            .process_context_mut()
            .node_connection_successor_set(indi_destination);
        calc_alg_context
            .process_context_mut()
            .conn_succ_set_mut(conn_succ_set)
            .insert_connection_successor(indi_source_id);
        if self.opt_incremental_compatible_expansion {
            // W3-DEFER[api]: linkCreationDirectlyChangedNeighbourConnectionUpdate(indiDestination,indiSource,true,calcAlgContext);
        }
        individual_link
    }

    // =======================================================================
    // addConceptToReapplyQueue overloads (cpp 26625 / 26632 / 26642 / 26653 / 26671).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addConceptToReapplyQueue`
    /// (the 3-arg dispatcher that derives the role from the concept, cpp 26625).
    pub fn add_concept_to_reapply_queue(
        &mut self,
        concept_descriptor: ConDescId,
        process_indi: NodeId,
        dependency_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let concept = calc_alg_context
            .process_context()
            .con_desc(concept_descriptor)
            .get_concept();
        let role = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_role();
        self.add_concept_to_reapply_queue_role(
            concept_descriptor,
            role,
            process_indi,
            true,
            dependency_track_point,
            calc_alg_context,
        );
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addConceptToReapplyQueue`
    /// (the `CRole*` + `isStaticDes` overload, cpp 26632).
    pub fn add_concept_to_reapply_queue_role(
        &mut self,
        concept_descriptor: ConDescId,
        role: RoleId,
        process_indi: NodeId,
        is_static_des: bool,
        dependency_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[memory-pool]: taskMemMan = calcAlgContext->getUsedProcessTaskMemoryAllocationManager();
        // W3-DEFER[api]: STATINC(INSERTCONCEPTREAPPLICATIONSCOUNT,calcAlgContext);
        let reapply_con_des = calc_alg_context
            .process_context_mut()
            .alloc_reapply_con_desc(ReapplyConceptDescriptor::new(
                concept_descriptor,
                dependency_track_point,
                is_static_des,
            ));
        // KM_BRIDGE_SEARCH_LOG: pair each ARM with its branch-epoch depth so a
        // fire at a SHALLOWER depth than every arm exposes a journal miss.
        if std::env::var_os("KM_BRIDGE_SEARCH_LOG").is_some() {
            let tag = calc_alg_context
                .ontology_arenas()
                .concept(
                    calc_alg_context
                        .process_context()
                        .con_desc(concept_descriptor)
                        .get_concept(),
                )
                .get_concept_tag();
            let opc = calc_alg_context
                .ontology_arenas()
                .concept(
                    calc_alg_context
                        .process_context()
                        .con_desc(concept_descriptor)
                        .get_concept(),
                )
                .get_operator_code();
            let label: Vec<i64> = {
                let pc = calc_alg_context.process_context();
                let ls = pc.node(process_indi).use_reapply_con_label_set;
                if ls.is_some() {
                    let mut v: Vec<i64> = pc
                        .label_set(ls)
                        .concept_des_dep_map
                        .iter()
                        .filter_map(|(t, d)| {
                            if d.concept_descriptor.is_none() {
                                None
                            } else if pc.con_desc(d.concept_descriptor).is_negated() {
                                Some(-*t)
                            } else {
                                Some(*t)
                            }
                        })
                        .collect();
                    v.sort_unstable();
                    v
                } else {
                    Vec::new()
                }
            };
            let m = format!(
                "reapply-arm node={} tag={} op={:?} static={} depth={} label={:?}",
                process_indi.index(),
                tag,
                opc,
                is_static_des,
                calc_alg_context.process_context().branch_epoch_depth(),
                label
            );
            self.ht_search_log(&m);
        }
        calc_alg_context
            .process_context_mut()
            .node_add_role_reapply_concept_descriptor(process_indi, role, reapply_con_des);
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addConceptToReapplyQueue`
    /// (the `CConcept*` + `negation` + `isStaticDes` overload, cpp 26642).
    pub fn add_concept_to_reapply_queue_concept(
        &mut self,
        concept_descriptor: ConDescId,
        concept: ConceptId,
        negation: bool,
        process_indi: NodeId,
        is_static_des: bool,
        dependency_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[memory-pool]: taskMemMan = calcAlgContext->getUsedProcessTaskMemoryAllocationManager();
        // W3-DEFER[api]: STATINC(INSERTCONCEPTREAPPLICATIONSCOUNT,calcAlgContext);
        let concept_tag = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_concept_tag();
        let mut reapply_con_des = CondensedReapplyConceptDescriptor::new(
            concept_descriptor,
            dependency_track_point,
            !negation,
        );
        reapply_con_des.static_descriptor = is_static_des;
        let reapply_con_des = calc_alg_context
            .process_context_mut()
            .alloc_cond_reapply_con_desc(reapply_con_des);
        calc_alg_context
            .process_context_mut()
            .node_add_concept_reapply_concept_descriptor_by_tag(
                process_indi,
                concept_tag,
                negation,
                reapply_con_des,
            );
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addConceptToReapplyQueue`
    /// (the `CRole*` + `CProcessingRestrictionSpecification*` overload, cpp 26653).
    pub fn add_concept_to_reapply_queue_role_restricted(
        &mut self,
        concept_descriptor: ConDescId,
        role: RoleId,
        process_indi: NodeId,
        proc_rest: ProcRestrictionHandle,
        dependency_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[memory-pool]: taskMemMan = calcAlgContext->getUsedProcessTaskMemoryAllocationManager();
        // W3-DEFER[api]: STATINC(INSERTCONCEPTREAPPLICATIONSCOUNT,calcAlgContext);
        let mut reapply_con_des =
            ReapplyConceptDescriptor::new(concept_descriptor, dependency_track_point, false);
        reapply_con_des.init_reapply_descriptor_restricted(
            concept_descriptor,
            dependency_track_point,
            proc_rest,
        );
        let reapply_con_des = calc_alg_context
            .process_context_mut()
            .alloc_reapply_con_desc(reapply_con_des);
        calc_alg_context
            .process_context_mut()
            .node_add_role_reapply_concept_descriptor(process_indi, role, reapply_con_des);
    }

    /// The at-most resume install (`applyATMOSTRule` cpp 15001–15005 through the
    /// `CProcessingRestrictionSpecification*` overload of `addConceptToReapplyQueue`).
    ///
    /// KONCLUDE-PORT-NOTE[api]: Konclude installs a CONSUMED-per-fire dynamic
    /// descriptor and re-installs after every application (each forked task has
    /// its own queue copy, so consumption cannot leak). The port's in-place
    /// backtracking cannot restore a cross-node queue consumption on branch
    /// advance — a consumed-but-not-reinstalled descriptor would permanently
    /// DISARM the ≤n restriction in the sibling world (missed merges = wrong
    /// SAT). The port therefore installs a STATIC descriptor (never consumed,
    /// fires on every later `role`-link) that CARRIES the branching-merging
    /// rest; the rest's arena slot is mutated in place across fires and its
    /// rollback at branch points is the epoch journal's job.
    pub fn add_concept_to_reapply_queue_role_restricted_static(
        &mut self,
        concept_descriptor: ConDescId,
        role: RoleId,
        process_indi: NodeId,
        proc_rest: ProcRestrictionHandle,
        dependency_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let mut reapply_con_des =
            ReapplyConceptDescriptor::new(concept_descriptor, dependency_track_point, true);
        reapply_con_des.processing_restriction = proc_rest;
        let reapply_con_des = calc_alg_context
            .process_context_mut()
            .alloc_reapply_con_desc(reapply_con_des);
        calc_alg_context
            .process_context_mut()
            .node_add_role_reapply_concept_descriptor(process_indi, role, reapply_con_des);
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addConceptToReapplyQueue`
    /// (the `CConcept*` + `negation` + `CProcessingRestrictionSpecification*` overload, cpp 26671).
    pub fn add_concept_to_reapply_queue_concept_restricted(
        &mut self,
        concept_descriptor: ConDescId,
        concept: ConceptId,
        negation: bool,
        process_indi: NodeId,
        proc_rest: ProcRestrictionHandle,
        dependency_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[memory-pool]: taskMemMan = calcAlgContext->getUsedProcessTaskMemoryAllocationManager();
        // W3-DEFER[api]: STATINC(INSERTCONCEPTREAPPLICATIONSCOUNT,calcAlgContext);
        let concept_tag = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_concept_tag();
        let mut reapply_con_des = CondensedReapplyConceptDescriptor::new(
            concept_descriptor,
            dependency_track_point,
            !negation,
        );
        reapply_con_des.init_reapply_descriptor_restricted(
            concept_descriptor,
            dependency_track_point,
            !negation,
            proc_rest,
        );
        let reapply_con_des = calc_alg_context
            .process_context_mut()
            .alloc_cond_reapply_con_desc(reapply_con_des);
        calc_alg_context
            .process_context_mut()
            .node_add_concept_reapply_concept_descriptor_by_tag(
                process_indi,
                concept_tag,
                negation,
                reapply_con_des,
            );
    }

    // =======================================================================
    // isConceptInReapplyQueue overloads (cpp 26674 / 26682).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::isConceptInReapplyQueue`
    /// (the `CConcept*` + `negation` overload, cpp 26674).
    pub fn is_concept_in_reapply_queue_concept(
        &mut self,
        concept_descriptor: ConDescId,
        concept: ConceptId,
        negation: bool,
        process_indi: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let concept_tag = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_concept_tag();
        calc_alg_context
            .process_context()
            .node_concept_reapply_queue_has_concept_descriptor_by_tag(
                process_indi,
                concept_tag,
                negation,
                concept_descriptor,
            )
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::isConceptInReapplyQueue`
    /// (the `CRole*` overload, cpp 26682).
    pub fn is_concept_in_reapply_queue_role(
        &mut self,
        concept_descriptor: ConDescId,
        role: RoleId,
        process_indi: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        calc_alg_context
            .process_context()
            .node_role_reapply_queue_has_concept_descriptor(process_indi, role, concept_descriptor)
    }

    // =======================================================================
    // Rule-counter getters (cpp 27650–27676): ALREADY ported as inline accessors
    // in `completion/algorithm.rs` (`applied_and_rule_count()` ..
    // `applied_total_rule_count()`); not re-defined here to avoid a duplicate
    // method definition on the shared impl.
    // =======================================================================
}
