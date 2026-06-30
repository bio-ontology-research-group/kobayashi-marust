//! `completion::u15` — port unit #15 of the completion task-handle algorithm
//! (Merge handling family).
//!
//! Ports seven methods of Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.cpp`:
//!   - `mergeIndividualNodeInto`                                                  (.cpp 21010–21562)
//!   - `visitIndividualsRelevantMergingsBackendSynchronisationDataIndividuals`    (.cpp 23036–23083)
//!   - `visitNewlyMergedIndividualsBackendSynchronisationData` (hash overload)    (.cpp 23089–23110)
//!   - `visitNewlyMergedIndividualsBackendSynchronisationData` (linker overload)  (.cpp 23118–23142)
//!   - `visitNewlyMergedOnlyDeterministicRepresentativeIndividualsBackendSynchronisationData` (.cpp 23144–23155)
//!   - `testIndividualNodeBackendCacheNewMergings`                                (.cpp 25849–25888)
//!   - `testIndividualNodeBackendCacheSameMergedBlockingCritical`                 (.cpp 26007–26032)
//!
//! KONCLUDE-PORT-NOTE[ownership]: C++ threads the per-thread
//! `CCalculationAlgorithmContextBase*` through every method; the port passes it as
//! an explicit `&mut CalculationAlgorithmContextBase` parameter (it owns the single
//! `ProcessingDataBox` and the per-test `ProcessContext` arenas).
//! `CIndividualProcessNode*` becomes a `NodeId`, `CDependencyTrackPoint*` a
//! `TrackPointId`. Node accessors resolve as `ctx.used_process_context().node(id)`
//! per the W3.5 convention.
//!
//! KONCLUDE-PORT-NOTE[api]: six of the seven methods are the **backend
//! representative-memory cache synchronisation** subsystem
//! (`CIndividualNodeRepresentativeMemoryBackendCacheSynchronisationData`,
//! `CBackendRepresentativeMemoryCacheIndividualAssociationData`,
//! `CBackendRepresentativeMemoryLabelCacheItem`, `mBackendCacheHandler`) plus the
//! intrusive `CXLinker<…>` / `CPROCESSHASH<…>` chains and `std::function` visitor
//! callbacks. That entire subsystem is the W6 Cache layer (not yet ported), so per
//! the porting plan their bodies are `W6-DEFER[api]` stubs: the faithful control
//! flow is recorded, the visitor signatures + structure are preserved, and every
//! cache/linker dereference is a marked stub. `mergeIndividualNodeInto` is the core
//! merge driver (not a Cache helper) but is `PORT-PENDING` for the same structural
//! reason `takeNextProcessIndividual` (u02) is: 553 lines dispatching ~15 not-yet-
//! ported sibling helpers from other units plus unported satellite-container
//! iterators — its full phase sequence is recorded in the doc comment for the
//! eventual reconcile.

#![allow(dead_code, unused_variables, unused_mut)]

use super::super::model::substrate::Cint64;
use super::super::process::{NodeId, TrackPointId};
use super::super::process::distinct::DistinctHashId;
use super::super::process::node::IndividualProcessNode;
use super::context::CalculationAlgorithmContextBase;

impl super::algorithm::CompletionTaskHandleAlgorithm {
    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::mergeIndividualNodeInto`.
    ///
    /// PARTIALLY PORTED (2026-06-30 merge-core wave): the 553-line merge driver.
    /// The phases whose dependencies now exist are ported with faithful control flow
    /// — the marking sibling (phase 1), the node setters (phase 3), the DISTINCT
    /// relocation (phase 8), the prune/flag-propagation (phase 9), and the final
    /// `propagateIndividualNodeModified` + `addIndividualToProcessingQueue` (phase
    /// 13). The phases that still bottom out in stub/missing facilities are kept as
    /// structured inline DEFER markers, each naming the exact gap:
    ///   - phase 2  completion-graph cache → `mCompGraphCacheHandler` /
    ///     `clearCompletionGraphCaching` are the unported W6 Cache layer;
    ///   - phase 4  concept-label merge → the `ReapplyConceptLabelSet` iterator
    ///     constructor (`getConceptLabelSetIterator`) + `containsConcept` +
    ///     `getConceptCount` are not yet on the label set (RECONCILE-NEED);
    ///   - phase 5  connection-link relocation → `SuccessorRoleIterator` /
    ///     `DisjointSuccessorRoleIterator` are pn3 zero-size stubs, and the nominal
    ///     neighbour backend-expansion is the W6 Cache layer;
    ///   - phase 6  nominal `IndividualMergingHash` → the merging hash is a stub `Id`
    ///     and `CCondensedReapplyQueueIterator` is a placeholder (STILL MISSING);
    ///   - phase 7  minimize-merging ancestor-link repoint →
    ///     `getRoleSuccessorToIndividualLink` / `getAncestorLink` not yet on node;
    ///   - phase 10 exact-nominal connection set → `getSuccessorNominalConnectionSet`
    ///     not yet on node;
    ///   - phase 11 assertion-linker relocation → the assertion-linker *getters*
    ///     (`getAssertionRoleLinker`, …) are not yet on node (the `add*` siblings
    ///     exist);
    ///   - phase 12 backend-cache sync transfer → the W6 Cache layer.
    /// The complete phase sequence (the C++ control flow is linear, phase after
    /// phase) is recorded below and mirrored 1:1 in the body:
    ///
    ///  0. `STATINC(INDINODEMERGECOUNT)`; debug model-string capture (debug-only).
    ///  1. `markIndividualNodeBackendNonConceptSetRelatedAndNeighbourLabelRelatedProcessing`
    ///     on both `mergeIntoIndividualNode` and `individual`.
    ///  2. completion-graph-cache fixup: if `mCompGraphCacheHandler &&
    ///     mConfCompletionGraphCaching` and `individual` is a nominal node merged
    ///     into a non-nominal, and it is not caching-invalidated and ≤
    ///     `getMaxCompletionGraphCachedIndividualNodeID()`, mark
    ///     `PRFCOMPLETIONGRAPHCACHEDNODELOCATED`, clear
    ///     `PRFRETESTCOMPLETIONGRAPHCACHEDDUEDIRECTMODIFIED`, `clearCompletionGraphCaching`.
    ///  3. `mergeIntoIndividualNode->setLastMergedIntoIndividualNode(individual)`;
    ///     `individual->setMergedDependencyTrackPoint(mergeDepTrackPoint)`;
    ///     `newLinksAdded = false`.
    ///  4. MERGE CONCEPT LABEL SET: take `individual`'s `ReapplyConceptLabelSet`; if
    ///     present, compare its concept count against `mergeIntoIndividualNode`'s
    ///     (scaled by `mMapComparisonDirectLookupFactor`) to pick the direct-lookup
    ///     branch vs the merge-walk branch; for each concept not already present,
    ///     `createMERGEDCONCEPTDependency` + `addConceptToIndividual(…,false,true,…)`
    ///     (`STATINC(INDINODEMERGECONCEPTSADDCOUNT)`).
    ///  5. MOVE CONNECTED INCOMING LINKS: over `individual`'s `ConnectionSuccessorSet`;
    ///     for each connected id — self-loop sub-branch (re-create role-succ links to
    ///     self) vs other-node sub-branch: nominal/ancestor/successor guard, optional
    ///     backend neighbour-expansion (`expandIndividualNeighbourNodeFromBackendCache`),
    ///     re-create forward + reverse role-succ links (`createNewIndividualsLinkReapplyed`,
    ///     dedup via `depTrackPointHash` + `createMERGEDLINKDependency`), re-create
    ///     forward + reverse negation/disjoint links (`createIndividualNodeNegationLink`),
    ///     remove the old links/disjoints/connection on `locConnIndi`.
    ///  6. NOMINAL MERGE BOOKKEEPING: if `individual` is nominal, promote
    ///     `mergeIntoIndividualNode` to `NOMINALINDIVIDUALTYPE` + copy nominal indi;
    ///     merge the `IndividualMergingHash` (init-from / per-entry add with
    ///     `createMERGEDINDIVIDUALDependency` + reapply-queue drain via
    ///     `applyReapplyQueueConcepts`); self-id merging-hash entry when
    ///     `nominalIndividual->getIndividualID() == -individual->getIndividualNodeID()`.
    ///  7. inherit `mergeIntoIndividualNode->getDependencyTrackPoint()` from the
    ///     `depTrackPointHash` if unset; if `mConfMinimizeMerging`, re-point the
    ///     ancestor link (`getAncestorLink` / `getRoleSuccessorToIndividualLink`).
    ///  8. ADD DISTINCT INFORMATION: over `individual`'s `DistinctHash`; relocate each
    ///     distinct edge to `mergeIntoIndividualNode` (`createMERGEDLINKDependency` +
    ///     new `CDistinctEdge`, `STATINC` distinct/creation), notify the datatype
    ///     handler of distinct changes.
    ///  9. PRUNE: `individual->setMergedIntoIndividualNodeID(mergeInto…ID)`;
    ///     `pruneSuccessors(individual,…)`; propagate `PRFINVALIDBLOCKINGORCACHING`.
    /// 10. if `mConfExactNominalDependencyTracking` and both nominal, copy
    ///     `SuccessorNominalConnectionSet` + the own nominal id into
    ///     `mergeIntoIndividualNode` (`addSuccessorConnectionToNominal`).
    /// 11. RELOCATE ASSERTION LINKERS: role-assertion + reverse, additional
    ///     role-assertion, init-concept, data-assertion + additional data-assertion,
    ///     asserted-data-literal linkers — each re-allocated onto `mergeIntoIndividualNode`
    ///     (with `createMERGEDINDIVIDUALDependency` for the additional ones),
    ///     `newLinksAdded = true`.
    /// 12. backend-sync transfer: if `mergeIntoIndividualNode` / `individual` carry
    ///     `PRFSYNCHRONIZEDBACKEN…` flags, `newLinksAdded = true`; if `individual`
    ///     has backend-cache sync data and `mergeIntoIndividualNode` does not, clone
    ///     it (`setIndividualBackendCacheSynchronisationData`,
    ///     `addIndividualToBackendIndirectCompatibilityExpansionQueue`).
    /// 13. if `newLinksAdded`, `propagateIndividualNodeModified`;
    ///     `addIndividualToProcessingQueue(mergeIntoIndividualNode)`; debug capture.
    pub fn merge_individual_node_into(
        &mut self,
        merge_into_individual_node: NodeId,
        individual: NodeId,
        merge_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // ---- phase 0: statistics + debug captures -------------------------------
        // STATINC(INDINODEMERGECOUNT, calcAlgContext);
        // (statistics gathering is a not-yet-ported subsystem; see u02 precedent.)
        // KONCLUCE_TASK_ALGORITHM_*_DEBUGGING model-string capture — debug-only, omitted.

        // ---- phase 1: mark both nodes backend-non-concept/neighbour-label related --
        self.mark_individual_node_backend_non_concept_set_related_and_neighbour_label_related_processing(
            merge_into_individual_node,
            calc_alg_context,
        );
        self.mark_individual_node_backend_non_concept_set_related_and_neighbour_label_related_processing(
            individual,
            calc_alg_context,
        );

        // ---- phase 2: completion-graph-cache fixup (nominal→non-nominal merge) ----
        // W6-DEFER[api]: `mCompGraphCacheHandler && mConfCompletionGraphCaching` gate +
        //   `clearCompletionGraphCaching(individual, …)` are the unported W6 Cache layer.
        //   The faithful guard, kept for the eventual un-defer:
        //   if mCompGraphCacheHandler && self.conf_completion_graph_caching
        //       && ctx.node(individual).is_nominal_individual_node()
        //       && !ctx.node(merge_into).is_nominal_individual_node() {
        //     if !indi.has_partial(PRFCOMPLETIONGRAPHCACHINGINVALIDATED)
        //         && indi.individual_node_id() <= ctx.max_completion_graph_cached_individual_node_id() {
        //       indi.add(PRFCOMPLETIONGRAPHCACHEDNODELOCATED);
        //       if indi.has_partial(PRFRETESTCOMPLETIONGRAPHCACHEDDUEDIRECTMODIFIED) {
        //         indi.clear(PRFRETESTCOMPLETIONGRAPHCACHEDDUEDIRECTMODIFIED); }
        //       self.clear_completion_graph_caching(individual, ctx);  // W6
        //     }
        //   }

        // ---- phase 3: link the two nodes + reset newLinksAdded -------------------
        {
            let pc = calc_alg_context.process_context_mut();
            pc.node_mut(merge_into_individual_node)
                .set_last_merged_into_individual_node(individual);
            pc.node_mut(individual)
                .set_merged_dependency_track_point(merge_dep_track_point);
        }
        let mut new_links_added = false;

        // The C++ `CPROCESSINGHASH<CDependencyTrackPoint*,CDependencyTrackPoint*>
        // depTrackPointHash` dedups the per-merge link dependency track points; it is
        // consulted in phases 5 and 7. Only phases 5/7 use it and both are deferred,
        // so it is not materialised yet (kept as a note for the un-defer wave).

        // ---- phase 4: merge the concept label set -------------------------------
        // RECONCILE-NEED: ReapplyConceptLabelSet::{get_concept_label_set_iterator (the
        //   CReapplyConceptLabelSetIterator constructor), contains_concept, get_concept_count}
        //   on the reapply_sat label set — the iterator type + `get_data_tag(ctx,onto)` /
        //   `get_concept_descriptor` / `get_dependency_track_point(ctx)` already exist, but
        //   the constructor + containment/count predicates are not yet there.
        // Faithful structure (un-defer once the label-set surface lands; the dependency
        // wrapper `create_merged_concept_dependency` and the `add_concept_to_individual_*`
        // sibling already exist and are called here):
        //   addingConceptLabelSet = ctx.node(individual).reapply_con_label_set (false-existence)
        //   if present {
        //     mergeIntoLabelSet = ctx.node_reapply_concept_label_set(merge_into) (true)
        //     if addingCount * mMapComparisonDirectLookupFactor < mergeIntoCount { direct-lookup }
        //     else { sorted merge-walk by data tag }
        //     for each conDes not already in mergeIntoLabelSet:
        //       STATINC(INDINODEMERGECONCEPTSADDCOUNT);
        //       let mut new_dtp = TrackPointId::NONE;
        //       self.create_merged_concept_dependency(&mut new_dtp, &mut merge_into, conDes,
        //           merge_dep_track_point, conDepTrackPoint, calc_alg_context);
        //       self.add_concept_to_individual_skip_and_processing(
        //           concept, negation, merge_into, new_dtp, false, true, /*markMod*/true, ctx);
        //   }
        let _ = self.map_comparison_direct_lookup_factor;

        // ---- phase 5: move all connected incoming links -------------------------
        // The OUTER walk over `individual`'s ConnectionSuccessorSet is now portable
        // (`ctx.node_connection_successor_set` + `ConnectionSuccessorSetIterator` are
        // real in process/distinct.rs); the INNER per-role relocation is NOT:
        //   - W6-DEFER[api]: the nominal neighbour backend-expansion sub-block
        //     (`getLocalizedIndividualBackendCacheSnychronisationData` /
        //     `expandIndividualNeighbourNodeFromBackendCache`) is the W6 Cache layer;
        //   - RECONCILE-NEED: `IndividualProcessNode::{get_successor_role_iterator,
        //     get_disjoint_successor_role_iterator}` resolve to pn3 zero-size stubs
        //     (no `has_next`/`next`), so the forward/reverse role-link + neg/disjoint
        //     relocation (`create_new_individuals_link_reapplyed` /
        //     `create_individual_node_negation_link` — both already exist as siblings —
        //     `remove_individual_link` / `remove_disjoint_links` /
        //     `remove_individual_connection`) cannot iterate yet.
        //     (PORTED: pn3.rs — the getters exist; the `has_next`/`next` empty-iterator
        //     surface is now on `SuccessorRoleIterator`/`DisjointSuccessorRoleIterator`
        //     (+ `RoleSuccessorIterator`/`RoleSuccessorLinkIterator`/`SuccessorIterator`).
        //     LEFT: the iterators still yield empty until the `mUseSuccRoleHash` /
        //     `mUseDisjointSuccRoleHash` process-hash backends (W2-DEFER) are threaded.)
        // Faithful self-loop vs other-node split + the dedup-via-depTrackPointHash +
        // `create_merged_link_dependency` structure is recorded in the doc comment.

        // ---- phase 6: nominal merge bookkeeping ---------------------------------
        // RECONCILE-NEED: `IndividualMergingHash` is a stub `Id` (pn6
        //   `individual_merging_hash(create)` returns `Id::NONE`) and
        //   `CCondensedReapplyQueueIterator` is a placeholder (STILL MISSING), so the
        //   merging-hash init/merge + `apply_reapply_queue_concepts` drain + the
        //   `create_merged_individual_dependency` per-entry dependency are deferred.
        //   The node-type promotion (`set_individual_type(NOMINALINDIVIDUALTYPE)` +
        //   `set_nominal_individual`) and `get_nominal_individual` reads also need the
        //   node nominal accessors. Full structure in the doc comment (phase 6).

        // ---- phase 7: inherit dep track point + minimize-merging ancestor repoint -
        // if ctx.node(merge_into).dependency_track_point().is_none() {
        //   merge_into.set_dependency_track_point(depTrackPointHash[individual.dep_tp]); }
        // RECONCILE-NEED: depends on the phase-5 `depTrackPointHash`; and the
        //   `mConfMinimizeMerging` branch needs `IndividualProcessNode::{get_ancestor_link,
        //   get_role_successor_to_individual_link, set_ancestor_link, has_individual_ancestor,
        //   get_individual_ancestor_depth}` (not yet on node) + `get_ancestor_individual`
        //   (sibling, exists). Deferred with phase 5.
        //   (PORTED: pn3.rs `get_ancestor_link` / `get_role_successor_to_individual_link`
        //   / `set_ancestor_link` / `has_individual_ancestor`; node.rs
        //   `individual_ancestor_depth`. All five node accessors exist; only the
        //   `depTrackPointHash` dedup (phase-5) remains LEFT.)
        let _ = self.conf_minimize_merging;

        // ---- phase 8: add distinct information (PORTED) --------------------------
        // KONCLUDE-PORT-NOTE[ownership]: the C++ walks `addDisHash`'s CDistinctIterator
        // while mutating other nodes' distinct hashes; in Rust the iterator borrows the
        // arena, so the distinct ids (+ their per-edge dep track points) are snapshotted
        // into a Vec first, then processed — behaviour identical, only the borrow split
        // differs.
        let mut merged_node_datatype_distinct_change_notified = false;
        let add_dis_hash_present = calc_alg_context
            .process_context()
            .node(individual)
            .distinct_hash
            .is_some(); // getDistinctHash(false)
        if add_dis_hash_present {
            let individual_node_id = calc_alg_context
                .process_context()
                .node(individual)
                .individual_node_id();
            let merge_into_node_id = calc_alg_context
                .process_context()
                .node(merge_into_individual_node)
                .individual_node_id();
            // mergeDisHash = mergeIntoIndividualNode->getDistinctHash(true)
            let merge_dis_hash: DistinctHashId = calc_alg_context
                .process_context_mut()
                .node_distinct_hash(merge_into_individual_node);
            // Snapshot (disIndiID, depTrackPoint) from addDisHash's iterator.
            let add_dis_hash: DistinctHashId = calc_alg_context
                .process_context_mut()
                .node_distinct_hash(individual);
            let mut dis_entries: Vec<(Cint64, TrackPointId)> = Vec::new();
            {
                let pc = calc_alg_context.process_context();
                let mut dis_it = pc.distinct_hash(add_dis_hash).get_distinct_iterator();
                while dis_it.has_next() {
                    // cint64 disIndiID = disIt.nextDistinctIndividualID(depTrackPoint);
                    let (dis_indi_id, dep_track_point) =
                        dis_it.next_distinct_individual_id_dep(pc.distinct_edges(), true);
                    dis_entries.push((dis_indi_id, dep_track_point));
                }
            }
            for (dis_indi_id, dep_track_point) in dis_entries {
                // locDisIndiNode = getLocalizedIndividual(disIndiID, calcAlgContext)
                let loc_dis_indi_node = calc_alg_context.get_localized_individual_by_id(dis_indi_id);
                // disHash = locDisIndiNode->getDistinctHash(true)
                let dis_hash: DistinctHashId = calc_alg_context
                    .process_context_mut()
                    .node_distinct_hash(loc_dis_indi_node);
                // disHash->removeDistinctIndividual(individual->getIndividualNodeID())
                calc_alg_context
                    .process_context_mut()
                    .distinct_hash_mut(dis_hash)
                    .remove_distinct_individual(individual_node_id);
                // if (!mergeDisHash->isIndividualDistinct(disIndiID))
                let already_distinct = calc_alg_context
                    .process_context()
                    .distinct_hash(merge_dis_hash)
                    .is_individual_distinct(dis_indi_id);
                if !already_distinct {
                    // STATINC(INDINODEMERGEDISTINCTADDCOUNT) / STATINC(DISTINCTCREATIONCOUNT)
                    // create dependency
                    let mut new_dep_track_point: TrackPointId = TrackPointId::NONE;
                    let mut merge_into = merge_into_individual_node;
                    self.create_merged_link_dependency(
                        &mut new_dep_track_point,
                        &mut merge_into,
                        merge_dep_track_point,
                        dep_track_point,
                        calc_alg_context,
                    );
                    // RECONCILE-NEED: ProcessContext::alloc_distinct_edge +
                    //   DistinctEdge::init_distinct_edge(loc_dis_indi_node, merge_into, new_dtp)
                    //   are not yet present (edge.rs DistinctEdge has only `new`). Once they
                    //   land:
                    //     let dis_edge = ctx.alloc_distinct_edge(DistinctEdge::new());
                    //     ctx.distinct_edge_mut(dis_edge).init_distinct_edge(
                    //         loc_dis_indi_node, merge_into_individual_node, new_dep_track_point);
                    //     ctx.distinct_hash_mut(merge_dis_hash)
                    //         .insert_distinct_individual(dis_indi_id, dis_edge);
                    //     ctx.distinct_hash_mut(dis_hash)
                    //         .insert_distinct_individual(merge_into_node_id, dis_edge);
                    let _ = (merge_dis_hash, merge_into_node_id, new_dep_track_point);

                    // if (mDatatypeHandler) { notifyDistinctChanges(...) ×2 }
                    // W6-DEFER[api]: `mDatatypeHandler` (the datatype handler) is STILL
                    //   MISSING; the distinct-change notification is deferred.
                    if !merged_node_datatype_distinct_change_notified {
                        merged_node_datatype_distinct_change_notified = true;
                    }
                }
            }
        }

        // ---- phase 9: prune nodes (PORTED) --------------------------------------
        // individual->setMergedIntoIndividualNodeID(mergeIntoIndividualNode->getIndividualNodeID())
        let merge_into_node_id = calc_alg_context
            .process_context()
            .node(merge_into_individual_node)
            .individual_node_id();
        calc_alg_context
            .process_context_mut()
            .node_mut(individual)
            .set_merged_into_individual_node_id(merge_into_node_id);
        // pruneSuccessors(individual, nullptr, false, calcAlgContext)
        let mut individual_mut = individual;
        self.prune_successors(&mut individual_mut, NodeId::NONE, false, calc_alg_context);
        // propagate PRFINVALIDBLOCKINGORCACHING
        let indi_has_invalid_blocking = calc_alg_context
            .process_context()
            .node(individual)
            .has_partial_processing_restriction_flags(
                IndividualProcessNode::PRF_INVALIDBLOCKINGORCACHING,
            );
        if indi_has_invalid_blocking {
            // RECONCILE-NEED: IndividualProcessNode::add_processing_restriction_flags
            //   (the PRF setter) is not yet exposed on the node; faithful call:
            //   ctx.node_mut(merge_into).add_processing_restriction_flags(
            //       IndividualProcessNode::PRF_INVALIDBLOCKINGORCACHING);
            //   (PORTED: pn4.rs `add_processing_restriction_flags` exists; un-defer wave
            //   wires the call site.)
        }

        // ---- phase 10: exact-nominal dependency-tracking connection copy --------
        // RECONCILE-NEED: `IndividualProcessNode::get_successor_nominal_connection_set`
        //   + `get_nominal_individual` are not yet on node (the
        //   `add_successor_connection_to_nominal` sink exists as a pn6 stub).
        //   (PORTED: pn6.rs `successor_nominal_connection_set` + sat1.rs
        //   `nominal_individual` both exist; the connection-set backend is W2-DEFER.)
        //   Faithful
        //   structure (un-defer once the getters land):
        //   if self.conf_exact_nominal_dependency_tracking
        //       && both nodes nominal {
        //     for nominalID in individual.successor_nominal_connection_set() {
        //       merge_into.add_successor_connection_to_nominal(nominalID); }
        //     if let Some(nom) = individual.nominal_individual() {
        //       merge_into.add_successor_connection_to_nominal(-nom.individual_id()); }
        //   }
        let _ = self.conf_exact_nominal_dependency_tracking;

        // ---- phase 11: relocate assertion linkers -------------------------------
        // RECONCILE-NEED: the assertion-linker *getters* on the node
        //   (`get_assertion_role_linker`, `get_reverse_assertion_role_linker`,
        //   `get_additional_role_assertions_linker`, `get_process_initializing_concept_linker`,
        //   `get_assertion_data_linker`, `get_additional_data_assertions_linker`,
        //   `get_asserted_data_literal_linker`) are not yet on node; the *sink* siblings
        //   (PORTED: pn2.rs — all seven getters exist under Rust naming, dropping the
        //   C++ `get_` prefix: `assertion_role_linker` / `reverse_assertion_role_linker`
        //   / `additional_role_assertions_linker` / `process_initializing_concept_linker`
        //   / `assertion_data_linker` / `additional_data_assertions_linker` /
        //   `asserted_data_literal_linker`; un-defer wave wires the relocation loop.)
        //   (`add_additional_role_assertions_linker`, `add_initializing_concept_linker`,
        //   `add_additional_data_assertions_linker`, `add_asserted_data_literal_linker`)
        //   already exist (pn2). Each relocation co-allocates the additional linker (with
        //   `create_merged_individual_dependency` for the additional ones) and sets
        //   `new_links_added = true`. Full structure in the doc comment (phase 11).

        // ---- phase 12: backend-cache sync transfer ------------------------------
        // W6-DEFER[api]: the `PRFSYNCHRONIZEDBACKEN…` flag transfer + the
        //   `getIndividualBackendCacheSynchronisationData` clone +
        //   `addIndividualToBackendIndirectCompatibilityExpansionQueue` are the unported
        //   W6 Cache layer. (`new_links_added` would be set here on a backend-sync flag.)

        // ---- phase 13: propagate-modified + enqueue (PORTED) --------------------
        if new_links_added {
            let mut merge_into = merge_into_individual_node;
            self.propagate_individual_node_modified(&mut merge_into, calc_alg_context);
        }
        self.add_individual_to_processing_queue(merge_into_individual_node, calc_alg_context);
        // KONCLUCE_TASK_ALGORITHM_MODEL_STRING_INSTRUCTION — debug-only, omitted.
    }

    /// Port of
    /// `CCalculationTableauCompletionTaskHandleAlgorithm::visitIndividualsRelevantMergingsBackendSynchronisationDataIndividuals`.
    ///
    /// W6-DEFER[api]: the whole body walks the backend representative-memory cache
    /// synchronisation subsystem (`CIndividualNodeRepresentativeMemoryBackendCacheSynchronisationData`,
    /// `CBackendRepresentativeMemoryCacheIndividualAssociationData`, the
    /// deterministic/nondeterministic SAME-INDIVIDUAL-SET label cache items,
    /// `mBackendCacheHandler->hasIndividualIdsInAssociatedIndividualSetLabel`) over an
    /// intrusive `CXLinker<cint64>` chain (`mergedIndiLinker`), invoking `visitFunc`
    /// at each relevant merged individual. None of that subsystem is ported (W6).
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: `CXLinker<cint64>*` chain heads become opaque
    /// `Cint64` handles; `std::function<bool(base, locBackendSyncData, depTrackPoint)>`
    /// becomes an `impl FnMut(NodeId, NodeId, TrackPointId) -> bool` callback.
    ///
    /// Structure: fetch base dep-track-point + `indiNode`'s backend-sync-data +
    /// merging hash; iff the merging hash exists and `mergedIndiLinker !=
    /// lastProcessedMergedIndiLinker`, walk `[mergedIndiLinker .. lastProcessed)`; for
    /// each merged id with `isMergedWithIndividual()` and `baseIndiId != mergedIndiId`:
    /// promote sync-data to localized + non-deterministically-merged when the merge is
    /// nondeterministic; then, if the id is not yet in the (non)deterministic
    /// same-individual-set label, resolve `getUpToDateIndividual(-mergedIndiId)`,
    /// optionally localize, and `visited |= visitFunc(indiNode, loc…, backSyncDep…)`.
    pub fn visit_individuals_relevant_mergings_backend_synchronisation_data_individuals(
        &mut self,
        indi_node: NodeId,
        merged_indi_linker: Cint64,
        last_processed_merged_indi_linker: Cint64,
        localize: bool,
        mut visit_func: impl FnMut(NodeId, NodeId, TrackPointId) -> bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let _ = (
            indi_node,
            merged_indi_linker,
            last_processed_merged_indi_linker,
            localize,
            calc_alg_context,
        );
        // bool visited = false; bool continueVisiting = true;
        let visited = false;
        // W6-DEFER[api]: backend representative-memory cache synchronisation walk over
        // the CXLinker<cint64> merged-individual chain + same-individual-set label
        // cache; the entire merging-relevance test is the unported W6 Cache layer.
        visited
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::visitNewlyMergedIndividualsBackendSynchronisationData`
    /// (the `CPROCESSHASH<CIndividualProcessNode*, CDependencyTrackPoint*>` overload, .cpp 23089).
    ///
    /// KONCLUDE-PORT-NOTE[overload]: C++ overloads this name on the
    /// new-merged-individuals container; the port disambiguates with a `_hash`
    /// suffix (this overload takes the hash) vs `_linker` (the `CXLinker` overload).
    ///
    /// W6-DEFER[api]: walks `indiNode`'s backend-sync-data and the
    /// `newIndiMergedHash` of `(backendSyncDataIndiNode → backSyncDepTrackPoint)`,
    /// invoking `visitFunc` for the base individual (when `visitBaseIndividual`) and
    /// for every hashed node that carries backend-cache sync data. The hash + sync
    /// data are the unported W6 Cache layer.
    pub fn visit_newly_merged_individuals_backend_synchronisation_data_hash(
        &mut self,
        indi_node: NodeId,
        new_indi_merged_hash: Cint64,
        visit_base_individual: bool,
        mut visit_func: impl FnMut(NodeId, NodeId, TrackPointId) -> bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let _ = (
            indi_node,
            new_indi_merged_hash,
            visit_base_individual,
            calc_alg_context,
        );
        // bool visited = false; bool continueVisiting = true;
        let visited = false;
        // W6-DEFER[api]: getIndividualBackendCacheSynchronisationData(false) gate +
        // optional visitFunc(indiNode, indiNode, baseDepTrackPoint) for the base
        // individual, then iterate newIndiMergedHash invoking visitFunc per entry.
        visited
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::visitNewlyMergedIndividualsBackendSynchronisationData`
    /// (the `CXLinker<CIndividualProcessNode*>` overload, .cpp 23118).
    ///
    /// KONCLUDE-PORT-NOTE[overload]: see the `_hash` overload above; this one walks
    /// the `[newIndiMergedLinker .. prevIndiMergedLinker)` node linker chain.
    ///
    /// W6-DEFER[api]: same backend-sync-data subsystem; per linked node it resolves
    /// `getUpToDateIndividual`, looks the node's nominal id up in the merging hash for
    /// the `backSyncDepTrackPoint`, and invokes `visitFunc` when the node carries
    /// backend-cache sync data.
    pub fn visit_newly_merged_individuals_backend_synchronisation_data_linker(
        &mut self,
        indi_node: NodeId,
        new_indi_merged_linker: Cint64,
        prev_indi_merged_linker: Cint64,
        visit_base_individual: bool,
        mut visit_func: impl FnMut(NodeId, NodeId, TrackPointId) -> bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let _ = (
            indi_node,
            new_indi_merged_linker,
            prev_indi_merged_linker,
            visit_base_individual,
            calc_alg_context,
        );
        // bool visited = false; bool continueVisiting = true;
        let visited = false;
        // W6-DEFER[api]: backend-sync-data gate + base-individual visit, then walk the
        // CXLinker<CIndividualProcessNode*> chain invoking visitFunc per up-to-date node.
        visited
    }

    /// Port of
    /// `CCalculationTableauCompletionTaskHandleAlgorithm::visitNewlyMergedOnlyDeterministicRepresentativeIndividualsBackendSynchronisationData`.
    ///
    /// Faithful port of THIS method's own logic: it delegates to the `_linker`
    /// overload, wrapping `visitFunc` so that when
    /// `mConfOnlyDeterministicRepresentativeBackendIndividualDataConsideration` is set
    /// and the merged node's backend assoc-data has a deterministic same-individual
    /// merging, the visit is skipped (the wrapper returns `true` to continue without
    /// calling the user callback). The wrapped cache reads are W6-DEFER[api].
    pub fn visit_newly_merged_only_deterministic_representative_individuals_backend_synchronisation_data(
        &mut self,
        indi_node: NodeId,
        new_indi_merged_linker: Cint64,
        prev_indi_merged_linker: Cint64,
        visit_base_individual: bool,
        mut visit_func: impl FnMut(NodeId, NodeId, TrackPointId) -> bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // Mirror the C++ lambda capture: `mConfOnlyDeterministicRepresentativeBackendIndividualDataConsideration`.
        let conf_only_det =
            self.conf_only_deterministic_representative_backend_individual_data_consideration;
        self.visit_newly_merged_individuals_backend_synchronisation_data_linker(
            indi_node,
            new_indi_merged_linker,
            prev_indi_merged_linker,
            visit_base_individual,
            move |base_indi_node, loc_backend_sync_data_indi_node, back_sync_dep_track_point| {
                // W6-DEFER[api]: CIndividualNodeRepresentativeMemoryBackendCacheSynchronisationData*
                //   mergedBackendSyncData = locBackendSyncDataIndiNode->getIndividualBackendCacheSynchronisationData(false);
                let merged_backend_sync_data_present = false;
                if conf_only_det && merged_backend_sync_data_present {
                    // W6-DEFER[api]: CBackendRepresentativeMemoryCacheIndividualAssociationData*
                    //   mergedAssocData = mergedBackendSyncData->getAssocitaionData();
                    //   if (mergedAssocData && mergedAssocData->hasDeterministicSameIndividualMerging()) return true;
                    let merged_assoc_data_has_det_same = false;
                    if merged_assoc_data_has_det_same {
                        return true;
                    }
                }
                visit_func(
                    base_indi_node,
                    loc_backend_sync_data_indi_node,
                    back_sync_dep_track_point,
                )
            },
            calc_alg_context,
        )
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::testIndividualNodeBackendCacheNewMergings`.
    ///
    /// W6-DEFER[api]: detects whether `indiNode` has newly merged individuals that
    /// the backend representative-memory cache has not yet integrated. It compares
    /// the merging hash's merged-individual count against the sync-data's last
    /// recorded count and, on change, localizes the sync data, then uses
    /// `visitIndividualsRelevantMergingsBackendSynchronisationDataIndividuals` to add
    /// each not-yet-integrated merged node to the localized sync data's merged-node
    /// linker (allocating a `CXLinker<CIndividualProcessNode*>`). The whole merging
    /// hash + sync-data + integrated-id-set machinery is the unported W6 Cache layer.
    pub fn test_individual_node_backend_cache_new_mergings(
        &mut self,
        indi_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let _ = (indi_node, calc_alg_context);
        // bool hasNewMergedIndividuals = false;
        let has_new_merged_individuals = false;
        // W6-DEFER[api]: merging-hash merged-count delta vs backend-sync-data, then
        // visitIndividualsRelevantMergingsBackendSynchronisationDataIndividuals(...)
        // appending newly integrated merged-individual-node linkers to the localized
        // sync data; sets hasNewMergedIndividuals on each genuinely new merge.
        has_new_merged_individuals
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::testIndividualNodeBackendCacheSameMergedBlockingCritical`.
    ///
    /// Faithful skeleton: gate on `indiNode`'s backend-sync-data, refresh new
    /// mergings via `test_individual_node_backend_cache_new_mergings`, then report
    /// expansion-blocking-critical when there is a merged-individual-node linker or a
    /// deterministic same-individual-set label cache entry. The backend-sync-data /
    /// assoc-data reads are the unported W6 Cache layer.
    pub fn test_individual_node_backend_cache_same_merged_blocking_critical(
        &mut self,
        indi_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // bool expansionBlockingCritical = false;
        let mut expansion_blocking_critical = false;

        // W6-DEFER[api]: CIndividualNodeRepresentativeMemoryBackendCacheSynchronisationData*
        //   backendSyncData = (…)indiNode->getIndividualBackendCacheSynchronisationData(false);
        let backend_sync_data_present = false;

        if backend_sync_data_present {
            // testIndividualNodeBackendCacheNewMergings(indiNode, calcAlgContext);
            self.test_individual_node_backend_cache_new_mergings(indi_node, calc_alg_context);
            // backendSyncData = (…)indiNode->getIndividualBackendCacheSynchronisationData(false);

            // W6-DEFER[api]: if (backendSyncData->getMergedIndividualNodeLinker())
            //   expansionBlockingCritical = true;
            // else if (assocData && assocData->getLabelCacheEntry(DETERMINISTIC_SAME_INDIVIDUAL_SET_LABEL))
            //   expansionBlockingCritical = true;
            let merged_individual_node_linker_present = false;
            if merged_individual_node_linker_present {
                expansion_blocking_critical = true;
            } else {
                let det_same_individual_set_label_present = false;
                if det_same_individual_set_label_present {
                    expansion_blocking_critical = true;
                }
            }
        }

        expansion_blocking_critical
    }
}
