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
//! cache/linker dereference is a marked stub. EXCEPTION: the `CXLinker` overload of
//! `visitNewlyMergedIndividualsBackendSynchronisationData` and its
//! `…OnlyDeterministicRepresentative…` wrapper are LIVE — their linkers are the
//! process-side `Vec<NodeId>` of `IndividualNodeBackendCacheSynchronisationData`,
//! which the u20 criticality predicates depend on. `mergeIndividualNodeInto` is the core
//! merge driver (not a Cache helper) but is `PORT-PENDING` for the same structural
//! reason `takeNextProcessIndividual` (u02) is: 553 lines dispatching ~15 not-yet-
//! ported sibling helpers from other units plus unported satellite-container
//! iterators — its full phase sequence is recorded in the doc comment for the
//! eventual reconcile.

#![allow(dead_code, unused_variables, unused_mut)]

use super::super::model::individual::{ReverseRoleAssertion, RoleAssertion};
use super::super::model::substrate::Cint64;
use super::super::process::distinct::DistinctHashId;
use super::super::process::edge::DistinctEdge;
use super::super::process::node::IndividualProcessNode;
use super::super::process::stubs::{
    AdditionalProcessDataAssertionsLinker, AdditionalProcessRoleAssertionsLinker,
    ProcessAssertedDataLiteralLinker,
};
use super::super::process::{ConDescId, NodeId, TrackPointId};
use super::context::CalculationAlgorithmContextBase;

impl super::algorithm::CompletionTaskHandleAlgorithm {
    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::mergeIndividualNodeInto`.
    ///
    /// PARTIALLY PORTED (2026-06-30 merge-core wave): the 553-line merge driver.
    /// The phases whose dependencies now exist are ported with faithful control flow
    /// — the marking sibling (phase 1), the node setters (phase 3), the DISTINCT
    /// relocation (phase 8), the prune/flag-propagation (phase 9), the
    /// assertion-linker relocation (phase 11), and the final
    /// `propagateIndividualNodeModified` + `addIndividualToProcessingQueue` (phase
    /// 13). The phases that still bottom out in stub/missing facilities are kept as
    /// structured inline DEFER markers, each naming the exact gap:
    ///   - phase 2  completion-graph cache → `mCompGraphCacheHandler` /
    ///     `clearCompletionGraphCaching` are the unported W6 Cache layer;
    ///   - phase 4  concept-label merge → the `ReapplyConceptLabelSet` iterator
    ///     constructor, `containsConcept`, and `getConceptCount` are live; the
    ///     phase body is still deferred until the whole label-merge branch is
    ///     wired through the existing dependency/add-concept helpers;
    ///   - phase 5  connection-link relocation → the iterator surface exists but
    ///     still awaits the threaded successor-role hash backends, and the nominal
    ///     neighbour backend-expansion is the W6 Cache layer;
    ///   - phase 6  nominal `IndividualMergingHash` → the merging hash is live,
    ///     but the `CCondensedReapplyQueueIterator` drain is still missing;
    ///   - phase 7  minimize-merging ancestor-link repoint → accessor surface is
    ///     live, but the phase depends on phase 5's per-merge dependency map;
    ///   - phase 10 exact-nominal connection set → live;
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
    /// Relocate `pred`'s role links that point at `from` onto `into` — the
    /// ht-scoped core of Konclude's merge phase 5 (cpp 21203–21232: per-link
    /// `createMERGEDLINKDependency` + `createNewIndividualsLinkReapplyed`).
    /// The install goes through `ht_install_role_successor_edge`, which fires
    /// the role reapply queues over the fresh link (the `…Reapplyed` part) —
    /// without this the predecessor LOSES its successor on a ≤n merge and
    /// successor-side recognitions (`D ⊑ ∀R⁻.E`) can never reach it again.
    /// Returns true iff a link was created.
    pub fn ht_relocate_incoming_links(
        &mut self,
        pred: NodeId,
        from: NodeId,
        into: NodeId,
        merge_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        if pred.is_none() || pred == into || from == into {
            return false;
        }
        let from_id = calc_alg_context
            .process_context()
            .node(from)
            .individual_node_id();
        // snapshot (role, link dep track point) of every pred→from link.
        let links: Vec<(super::super::model::RoleId, TrackPointId)> = {
            let pc = calc_alg_context.process_context();
            let mut it = pc.node_successor_role_iterator(pred, from_id);
            let mut v = Vec::new();
            while it.has_next() {
                let link = it.next(true);
                if link.is_none() {
                    continue;
                }
                let e = pc.edge(link);
                v.push((e.get_link_role(), e.get_dependency_track_point()));
            }
            v
        };
        let mut added = false;
        for (role, link_dep_track_point) in links {
            // hasRoleSuccessorToIndividual(role, into) — skip existing.
            let exists = self
                .ht_role_successor_links(pred, role, calc_alg_context)
                .iter()
                .any(|&(_, s)| s == into);
            if exists {
                continue;
            }
            // createMERGEDLINKDependency(newDtp, mergeInto, mergeDtp, prevLinkDtp)
            let mut new_dep_track_point = TrackPointId::NONE;
            let mut into_mut = into;
            self.create_merged_link_dependency(
                &mut new_dep_track_point,
                &mut into_mut,
                merge_dep_track_point,
                link_dep_track_point,
                calc_alg_context,
            );
            self.ht_install_role_successor_edge(
                pred,
                into,
                role,
                new_dep_track_point,
                calc_alg_context,
            );
            added = true;
        }
        added
    }

    pub fn merge_individual_node_into(
        &mut self,
        merge_into_individual_node: NodeId,
        individual: NodeId,
        merge_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // A representative-cache expansion block is valid only for the exact
        // cached concept/neighbour state. Konclude invalidates both
        // synchronization records before merging and carries the assertions
        // under the merge dependency. Do the same before phase 1 mutates
        // either completion node.
        self.invalidate_native_nominal_backend_blocking(
            merge_into_individual_node,
            calc_alg_context,
        );
        self.invalidate_native_nominal_backend_blocking(individual, calc_alg_context);

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

        // ---- phase 4: merge the concept label set (PORTED) ------------------------
        // cpp 21077–21141: every concept of `individual`'s label whose TAG is not yet
        // in `merge_into`'s label is added under a MERGEDCONCEPT dependency.
        // Konclude's contains test is `containsConcept(concept, nullptr)` — ANY
        // polarity — because a cross-polarity pair is caught BEFORE the merge by
        // `isIndividualNodesMergeable` → `isLabelConceptClashSet` (cpp 20714/20867).
        // KONCLUDE-PORT-NOTE[api]: the C++ picks direct-lookup vs sorted merge-walk
        // purely as a map-size heuristic (mMapComparisonDirectLookupFactor); the port
        // always direct-looks-up — identical insertions either way.
        let _ = self.map_comparison_direct_lookup_factor;
        let adding_concept_label_set = calc_alg_context
            .process_context()
            .node(individual)
            .use_reapply_con_label_set;
        if adding_concept_label_set.is_some() {
            // snapshot (conDes, depTrackPoint) — the iterator borrows the context
            // immutably while add_concept_to_individual mutates it.
            let adding: Vec<(ConDescId, TrackPointId)> = {
                let pc = calc_alg_context.process_context();
                let ls = pc.label_set(adding_concept_label_set);
                let mut it = ls.get_concept_label_set_iterator(true, true, false);
                let mut v = Vec::new();
                while it.has_next() {
                    let cd = it.get_concept_descriptor();
                    if cd.is_some() {
                        v.push((cd, it.get_dependency_track_point(pc)));
                    }
                    it.move_next(pc);
                }
                v
            };
            let merge_into_label_set = calc_alg_context
                .process_context_mut()
                .node_reapply_concept_label_set(merge_into_individual_node);
            for (con_des, con_dep_track_point) in adding {
                let (concept, negation) = {
                    let pc = calc_alg_context.process_context();
                    (
                        pc.con_desc(con_des).get_concept(),
                        pc.con_desc(con_des).is_negated(),
                    )
                };
                // containsConcept(concept, nullptr) — ANY polarity, tag-RESOLVED
                // (ls1::has_concept is a W2-DEFER stub; see u35 resolved helpers).
                let contained_any_polarity = self.contains_individual_node_concept_label(
                    merge_into_label_set,
                    concept,
                    None,
                    calc_alg_context,
                );
                if !contained_any_polarity {
                    // STATINC(INDINODEMERGECONCEPTSADDCOUNT)
                    let mut new_dep_track_point = TrackPointId::NONE;
                    let mut merge_into_mut = merge_into_individual_node;
                    self.create_merged_concept_dependency(
                        &mut new_dep_track_point,
                        &mut merge_into_mut,
                        con_des,
                        merge_dep_track_point,
                        con_dep_track_point,
                        calc_alg_context,
                    );
                    self.add_concept_to_individual(
                        concept,
                        negation,
                        &mut merge_into_mut,
                        new_dep_track_point,
                        false,
                        true,
                        calc_alg_context,
                    );
                    // the C++ insert-clash THROWS out of the merge — mirror via the
                    // pending signal (caller handles it like the exception).
                    if calc_alg_context.has_pending_signal() {
                        return;
                    }
                }
            }
        }

        // ---- phase 5: move connected incoming links (PORTED, ancestor-scoped) ----
        // Konclude's outer walk covers `individual`'s ConnectionSuccessorSet; for a
        // BLOCKABLE tree node the processed entries reduce to the tree PREDECESSOR
        // (the `individual->isIndividualAncestor(locConnIndi)` arm) — children fail
        // every arm and are handled by prune + re-derivation from the unioned label.
        // The ht layer maintains no connection-successor sets, so the port relocates
        // from the ancestor directly (the ≤n-merge caller additionally relocates from
        // the counted parent; see `ht_apply_atmost_merge`). The old predecessor→
        // `individual` links stay in the hashes — `ht_role_successor_links` filters
        // merged/purged ghosts, realising Konclude's `removeIndividualLink`.
        {
            let mut individual_mut = individual;
            let from_ancestor = self.get_ancestor_individual(&mut individual_mut, calc_alg_context);
            if from_ancestor.is_some() {
                new_links_added |= self.ht_relocate_incoming_links(
                    from_ancestor,
                    individual,
                    merge_into_individual_node,
                    merge_dep_track_point,
                    calc_alg_context,
                );
            }
        }
        // W6-DEFER[api]: the nominal neighbour backend-expansion sub-block + the
        // neg/disjoint-link relocation remain deferred with the W6 Cache layer.

        // ---- phase 6: nominal merge bookkeeping ---------------------------------
        // `IndividualMergingHash` and the node nominal accessors are live, but
        // the CCondensedReapplyQueueIterator drain is still missing. The
        // merging-hash init/merge + `apply_reapply_queue_concepts` drain + the
        // `create_merged_individual_dependency` per-entry dependency remain deferred.
        // Full structure in the doc comment (phase 6).

        // ---- phase 7: inherit dep track point + minimize-merging ancestor repoint -
        // if ctx.node(merge_into).dependency_track_point().is_none() {
        //   merge_into.set_dependency_track_point(depTrackPointHash[individual.dep_tp]); }
        // The minimize-merging node accessors are live; this phase remains deferred
        // with phase 5 because it depends on the per-merge `depTrackPointHash` dedup.
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
                let loc_dis_indi_node =
                    calc_alg_context.get_localized_individual_by_id(dis_indi_id);
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
                    let dis_edge = calc_alg_context
                        .process_context_mut()
                        .alloc_distinct_edge(DistinctEdge::new());
                    calc_alg_context
                        .process_context_mut()
                        .distinct_edge_mut(dis_edge)
                        .init_distinct_edge(
                            loc_dis_indi_node,
                            merge_into_individual_node,
                            new_dep_track_point,
                        );
                    calc_alg_context
                        .process_context_mut()
                        .distinct_hash_mut(merge_dis_hash)
                        .insert_distinct_individual(dis_indi_id, dis_edge);
                    calc_alg_context
                        .process_context_mut()
                        .distinct_hash_mut(dis_hash)
                        .insert_distinct_individual(merge_into_node_id, dis_edge);

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
            calc_alg_context
                .process_context_mut()
                .node_mut(merge_into_individual_node)
                .add_processing_restriction_flags(
                    IndividualProcessNode::PRF_INVALIDBLOCKINGORCACHING,
                );
        }

        // ---- phase 10: exact-nominal dependency-tracking connection copy --------
        if self.conf_exact_nominal_dependency_tracking {
            let (merge_into_nominal, individual_nominal, individual_nominal_id) = {
                let pc = calc_alg_context.process_context();
                (
                    pc.node(merge_into_individual_node)
                        .is_nominal_individual_node(),
                    pc.node(individual).is_nominal_individual_node(),
                    pc.node(individual).nominal_individual(),
                )
            };
            if merge_into_nominal && individual_nominal {
                let connected_nominals = calc_alg_context
                    .process_context()
                    .node_successor_connected_nominals(individual);
                for nominal_id in connected_nominals {
                    calc_alg_context
                        .process_context_mut()
                        .node_add_successor_connection_to_nominal(
                            merge_into_individual_node,
                            nominal_id,
                        );
                }
                if individual_nominal_id.is_some() {
                    let nominal_id = calc_alg_context
                        .ontology_arenas()
                        .individual(individual_nominal_id)
                        .get_individual_id();
                    calc_alg_context
                        .process_context_mut()
                        .node_add_successor_connection_to_nominal(
                            merge_into_individual_node,
                            -nominal_id,
                        );
                }
            }
        }

        // ---- phase 11: relocate assertion linkers -------------------------------
        let (
            nominal_individual,
            role_ass_linker,
            reverse_role_ass_linker,
            role_assertions,
            reverse_role_assertions,
            assertion_owner_tag,
            initializing_concepts,
            data_ass_linker,
            mut additional_role_entries,
            mut additional_data_entries,
            mut asserted_data_literal_entries,
        ) = {
            let pc = calc_alg_context.process_context();
            let node = pc.node(individual);
            let nominal_individual = node.nominal_individual().raw;
            let role_ass_linker = node.assertion_role_linker();
            let reverse_role_ass_linker = node.reverse_assertion_role_linker();
            let role_assertions = node.assertion_role_assertions().to_vec();
            let reverse_role_assertions = node.reverse_assertion_role_assertions().to_vec();
            let assertion_owner_tag = -node.individual_node_id();
            let initializing_concepts = node.process_initializing_concept_linker().to_vec();
            let data_ass_linker = node.assertion_data_linker();

            let mut additional_role_entries = Vec::new();
            let mut role_it = node.additional_role_assertions_linker();
            while role_it.is_some() {
                let linker = pc.additional_role_assertion_linker(role_it);
                additional_role_entries.push((
                    linker.individual(),
                    linker.role_assertion_linker(),
                    linker.reverse_role_assertion_linker(),
                    linker.dependency_track_point(),
                ));
                role_it = linker.next();
            }

            let mut additional_data_entries = Vec::new();
            let mut data_it = node.additional_data_assertions_linker();
            while data_it.is_some() {
                let linker = pc.additional_data_assertion_linker(data_it);
                additional_data_entries.push((
                    linker.individual(),
                    linker.data_assertion_linker(),
                    linker.dependency_track_point(),
                ));
                data_it = linker.next();
            }

            let mut asserted_data_literal_entries = Vec::new();
            let mut literal_it = node.asserted_data_literal_linker();
            while literal_it.is_some() {
                let linker = pc.process_asserted_data_literal_linker(literal_it);
                asserted_data_literal_entries
                    .push((linker.data_literal(), linker.dependency_track_point()));
                literal_it = linker.next();
            }

            (
                nominal_individual,
                role_ass_linker,
                reverse_role_ass_linker,
                role_assertions,
                reverse_role_assertions,
                assertion_owner_tag,
                initializing_concepts,
                data_ass_linker,
                additional_role_entries,
                additional_data_entries,
                asserted_data_literal_entries,
            )
        };

        if role_ass_linker.is_some() || reverse_role_ass_linker.is_some() {
            let mut linker = AdditionalProcessRoleAssertionsLinker::new();
            linker.init_additional_process_role_assertions_linker(
                nominal_individual,
                role_ass_linker,
                reverse_role_ass_linker,
                merge_dep_track_point,
            );
            let pc = calc_alg_context.process_context_mut();
            let linker = pc.alloc_additional_role_assertion_linker(linker);
            let old_head = pc
                .node(merge_into_individual_node)
                .additional_role_assertions_linker();
            pc.additional_role_assertion_linker_mut(linker)
                .set_next(old_head);
            pc.node_mut(merge_into_individual_node)
                .set_additional_role_assertions_linker(linker);
            new_links_added = true;
        }

        // Rust's native ABox bridge stores the same assertion chains by value
        // because the C++ intrusive-linker addresses are not stable here.
        // Preserve them on the surviving node and materialize only newly
        // transferred assertions with the merge dependency. Existing target
        // assertions retain their original derivations; a later lazy replay
        // may see these values again, but the role-link deduplication makes
        // that idempotent.
        let mut transferred_role_assertions: Vec<RoleAssertion> = Vec::new();
        let mut transferred_reverse_role_assertions: Vec<ReverseRoleAssertion> = Vec::new();
        {
            let pc = calc_alg_context.process_context();
            let target = pc.node(merge_into_individual_node);
            for assertion in role_assertions {
                if !target.assertion_role_assertions().contains(&assertion) {
                    transferred_role_assertions.push(assertion);
                }
            }
            for assertion in reverse_role_assertions {
                if !target
                    .reverse_assertion_role_assertions()
                    .contains(&assertion)
                {
                    transferred_reverse_role_assertions.push(assertion);
                }
            }
        }
        if !transferred_role_assertions.is_empty()
            || !transferred_reverse_role_assertions.is_empty()
        {
            {
                let target = calc_alg_context
                    .process_context_mut()
                    .node_mut(merge_into_individual_node);
                let mut combined = target.assertion_role_assertions().to_vec();
                combined.extend(transferred_role_assertions.iter().copied());
                target.set_assertion_role_assertions(combined);
                let mut combined_reverse = target.reverse_assertion_role_assertions().to_vec();
                combined_reverse.extend(transferred_reverse_role_assertions.iter().copied());
                target.set_reverse_assertion_role_assertions(combined_reverse);
            }
            for assertion in transferred_role_assertions {
                if assertion.individual.is_none()
                    || assertion.individual.index()
                        >= calc_alg_context.ontology_arenas().individual_count() as usize
                {
                    calc_alg_context.raise_stop(false);
                    return;
                }
                let target_tag = calc_alg_context
                    .ontology_arenas()
                    .individual(assertion.individual)
                    .get_individual_id();
                if !self.install_native_role_assertion_edge(
                    merge_into_individual_node,
                    assertion.role,
                    target_tag,
                    merge_dep_track_point,
                    calc_alg_context,
                ) {
                    calc_alg_context.raise_stop(false);
                    return;
                }
            }
            if assertion_owner_tag < 0 {
                calc_alg_context.raise_stop(false);
                return;
            }
            for assertion in transferred_reverse_role_assertions {
                if assertion.individual.is_none()
                    || assertion.individual.index()
                        >= calc_alg_context.ontology_arenas().individual_count() as usize
                {
                    calc_alg_context.raise_stop(false);
                    return;
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
                        assertion_owner_tag,
                        merge_dep_track_point,
                        calc_alg_context,
                    )
                {
                    calc_alg_context.raise_stop(false);
                    return;
                }
            }
            new_links_added = true;
        }
        for (source_individual, role_linker, reverse_role_linker, dep_track_point) in
            additional_role_entries.drain(..)
        {
            let mut new_indi_dep_track_point = TrackPointId::NONE;
            let mut merge_into = merge_into_individual_node;
            self.create_merged_individual_dependency(
                &mut new_indi_dep_track_point,
                &mut merge_into,
                merge_dep_track_point,
                dep_track_point,
                calc_alg_context,
            );

            let mut linker = AdditionalProcessRoleAssertionsLinker::new();
            linker.init_additional_process_role_assertions_linker(
                source_individual,
                role_linker,
                reverse_role_linker,
                new_indi_dep_track_point,
            );
            let pc = calc_alg_context.process_context_mut();
            let linker = pc.alloc_additional_role_assertion_linker(linker);
            let old_head = pc
                .node(merge_into_individual_node)
                .additional_role_assertions_linker();
            pc.additional_role_assertion_linker_mut(linker)
                .set_next(old_head);
            pc.node_mut(merge_into_individual_node)
                .set_additional_role_assertions_linker(linker);
            new_links_added = true;
        }

        for init_linker in initializing_concepts {
            calc_alg_context
                .process_context_mut()
                .node_mut(merge_into_individual_node)
                .add_initializing_concept_linker(vec![init_linker]);
        }

        if data_ass_linker.is_some() {
            let mut linker = AdditionalProcessDataAssertionsLinker::new();
            linker.init_additional_process_data_assertions_linker(
                nominal_individual,
                data_ass_linker,
                merge_dep_track_point,
            );
            let pc = calc_alg_context.process_context_mut();
            let linker = pc.alloc_additional_data_assertion_linker(linker);
            let old_head = pc
                .node(merge_into_individual_node)
                .additional_data_assertions_linker();
            pc.additional_data_assertion_linker_mut(linker)
                .set_next(old_head);
            pc.node_mut(merge_into_individual_node)
                .set_additional_data_assertions_linker(linker);
            new_links_added = true;
        }
        for (source_individual, data_linker, dep_track_point) in additional_data_entries.drain(..) {
            let mut new_indi_dep_track_point = TrackPointId::NONE;
            let mut merge_into = merge_into_individual_node;
            self.create_merged_individual_dependency(
                &mut new_indi_dep_track_point,
                &mut merge_into,
                merge_dep_track_point,
                dep_track_point,
                calc_alg_context,
            );

            let mut linker = AdditionalProcessDataAssertionsLinker::new();
            linker.init_additional_process_data_assertions_linker(
                source_individual,
                data_linker,
                new_indi_dep_track_point,
            );
            let pc = calc_alg_context.process_context_mut();
            let linker = pc.alloc_additional_data_assertion_linker(linker);
            let old_head = pc
                .node(merge_into_individual_node)
                .additional_data_assertions_linker();
            pc.additional_data_assertion_linker_mut(linker)
                .set_next(old_head);
            pc.node_mut(merge_into_individual_node)
                .set_additional_data_assertions_linker(linker);
            new_links_added = true;
        }

        for (data_literal, dep_track_point) in asserted_data_literal_entries.drain(..) {
            let mut new_indi_dep_track_point = TrackPointId::NONE;
            let mut merge_into = merge_into_individual_node;
            self.create_merged_individual_dependency(
                &mut new_indi_dep_track_point,
                &mut merge_into,
                merge_dep_track_point,
                dep_track_point,
                calc_alg_context,
            );

            let mut linker = ProcessAssertedDataLiteralLinker::new();
            linker.init_process_data_literal_linker(data_literal, new_indi_dep_track_point);
            let pc = calc_alg_context.process_context_mut();
            let linker = pc.alloc_process_asserted_data_literal_linker(linker);
            let old_head = pc
                .node(merge_into_individual_node)
                .asserted_data_literal_linker();
            pc.process_asserted_data_literal_linker_mut(linker)
                .set_next(old_head);
            pc.node_mut(merge_into_individual_node)
                .set_asserted_data_literal_linker(linker);
            new_links_added = true;
        }

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

        // Unsat-cache probe on the merged node (cpp 15457:
        // `testUnsatisfiableCacheForMergedIndividualNodes`, constant-true —
        // Konclude tests right after `getMergedIndividualNodes` in the merging
        // loop; probing at the shared primitive's tail covers every KM merge
        // path identically). Pending-gated: the merge itself may have raised
        // a clash, and `raise_clash` overwrites the signal.
        if !calc_alg_context.has_pending_signal() {
            self.test_individual_node_unsatisfiable_cached(
                merge_into_individual_node,
                calc_alg_context,
            );
        }
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
    /// LIVE. Faithful transcription of cpp 23118–23142:
    ///
    /// ```text
    /// visited = false; continueVisiting = true;
    /// depTrackPoint = calcAlgContext->getBaseDependencyNode()->getContinueDependencyTrackPoint();
    /// backendSyncData = indiNode->getIndividualBackendCacheSynchronisationData(false);
    /// if (backendSyncData && visitBaseIndividual) {
    ///   continueVisiting = visitFunc(indiNode, indiNode, depTrackPoint); visited = true; }
    /// if (newIndiMergedLinker != prevIndiMergedLinker) {
    ///   mergingHash = indiNode->getIndividualMergingHash(false);
    ///   for (it = newIndiMergedLinker; it && it != prevIndiMergedLinker && continueVisiting; it = it->getNext()) {
    ///     backendSyncDataIndiNode = getUpToDateIndividual(it->getData(), calcAlgContext);
    ///     mergingData = mergingHash->value(backendSyncDataIndiNode->getNominalIndividual()->getIndividualID());
    ///     backSyncDepTrackPoint = mergingData.getDependencyTrackPoint();
    ///     if (backendSyncDataIndiNode->getIndividualBackendCacheSynchronisationData(false)) {
    ///       continueVisiting = visitFunc(indiNode, backendSyncDataIndiNode, backSyncDepTrackPoint);
    ///       visited = true; } } }
    /// return visited;
    /// ```
    ///
    /// The gate that matters to every caller is the LAST one: a merged node is only
    /// visited when it itself carries backend-cache synchronisation data, i.e. when
    /// it is a representative individual the backend cache knows about. A merged node
    /// without sync data is walked over silently.
    ///
    /// KM-DEVIATION[linker]: the C++ `CXLinker` is a prepend-list, so
    /// `prevIndiMergedLinker` is a *suffix* of `newIndiMergedLinker` and the
    /// `it != prevIndiMergedLinker` bound walks exactly the newly prepended prefix.
    /// KM stores both as `Vec<NodeId>` snapshots, so the same window is "the entries
    /// of `new` that `prev` does not already hold"; that coincides with the pointer
    /// walk whenever `prev` is a suffix of `new` and degrades to "every entry is new"
    /// when it is not, which never skips a visit.
    pub fn visit_newly_merged_individuals_backend_synchronisation_data_linker(
        &mut self,
        indi_node: NodeId,
        new_indi_merged_linker: &[NodeId],
        prev_indi_merged_linker: &[NodeId],
        visit_base_individual: bool,
        visit_func: &mut dyn FnMut(NodeId, NodeId, TrackPointId) -> bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // bool visited = false; bool continueVisiting = true;
        let mut visited = false;
        let mut continue_visiting = true;
        // depTrackPoint = calcAlgContext->getBaseDependencyNode()->getContinueDependencyTrackPoint();
        let base_dep_node = calc_alg_context.base_dependency_node();
        let dep_track_point = if base_dep_node.is_some() {
            calc_alg_context
                .process_context_mut()
                .materialize_continue_dependency_track_point(base_dep_node)
        } else {
            TrackPointId::NONE
        };
        // backendSyncData = indiNode->getIndividualBackendCacheSynchronisationData(false);
        let backend_sync_data = calc_alg_context
            .process_context()
            .node(indi_node)
            .individual_backend_cache_synchronisation_data(false);

        if backend_sync_data.is_some() && visit_base_individual {
            continue_visiting = visit_func(indi_node, indi_node, dep_track_point);
            visited = true;
        }

        if new_indi_merged_linker != prev_indi_merged_linker {
            for &merged in new_indi_merged_linker {
                if !continue_visiting {
                    break;
                }
                // the `it != prevIndiMergedLinker` window, see KM-DEVIATION[linker]
                if prev_indi_merged_linker.contains(&merged) {
                    continue;
                }
                // backendSyncDataIndiNode = getUpToDateIndividual(…, calcAlgContext);
                let backend_sync_data_indi_node =
                    self.get_up_to_date_individual(merged, calc_alg_context);
                // mergingData = mergingHash->value(…->getNominalIndividual()->getIndividualID());
                let back_sync_dep_track_point = {
                    let process_context = calc_alg_context.process_context();
                    let merging_hash = process_context.node(indi_node).use_individual_merging_hash;
                    let merged_nominal = process_context
                        .node(backend_sync_data_indi_node)
                        .nominal_individual();
                    if merging_hash.is_some() && merged_nominal.is_some() {
                        let merged_indi_id = calc_alg_context
                            .ontology_arenas()
                            .individual(merged_nominal)
                            .get_individual_id();
                        process_context
                            .individual_merging_hash(merging_hash)
                            .get(merged_indi_id)
                            .map(|merging_data| merging_data.get_dependency_track_point())
                            .unwrap_or(TrackPointId::NONE)
                    } else {
                        TrackPointId::NONE
                    }
                };
                // if (backendSyncDataIndiNode->getIndividualBackendCacheSynchronisationData(false))
                let merged_backend_sync_data = calc_alg_context
                    .process_context()
                    .node(backend_sync_data_indi_node)
                    .individual_backend_cache_synchronisation_data(false);
                if merged_backend_sync_data.is_none() {
                    continue;
                }
                continue_visiting = visit_func(
                    indi_node,
                    backend_sync_data_indi_node,
                    back_sync_dep_track_point,
                );
                visited = true;
            }
        }

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
        new_indi_merged_linker: &[NodeId],
        prev_indi_merged_linker: &[NodeId],
        visit_base_individual: bool,
        visit_func: &mut dyn FnMut(NodeId, NodeId, TrackPointId) -> bool,
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
            &mut |base_indi_node, loc_backend_sync_data_indi_node, back_sync_dep_track_point| {
                // mergedBackendSyncData = locBackendSyncDataIndiNode->getIndividualBackendCacheSynchronisationData(false);
                // — the `_linker` overload above only forwards nodes that carry it, so
                // it is present for every node reaching this wrapper.
                let merged_backend_sync_data_present = true;
                if conf_only_det && merged_backend_sync_data_present {
                    // W6-DEFER[api]: CBackendRepresentativeMemoryCacheIndividualAssociationData*
                    //   mergedAssocData = mergedBackendSyncData->getAssocitaionData();
                    //   if (mergedAssocData && mergedAssocData->hasDeterministicSameIndividualMerging()) return true;
                    //
                    // The association arena lives in the (unported-to-this-context)
                    // W6 cache layer, so this SKIP stays deferred. It can only remove
                    // visits, so leaving it inactive never skips work — the same
                    // fail-open direction the rest of the backend-cache ports take.
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

#[cfg(test)]
mod tests {
    use crate::konclude_ht::completion::algorithm::CompletionTaskHandleAlgorithm;
    use crate::konclude_ht::completion::context::CalculationAlgorithmContextBase;
    use crate::konclude_ht::model::individual::{Individual, ReverseRoleAssertion, RoleAssertion};
    use crate::konclude_ht::model::role::Role;
    use crate::konclude_ht::model::substrate::{Id, NegLink};
    use crate::konclude_ht::model::ConceptId;
    use crate::konclude_ht::process::edge::DistinctEdge;
    use crate::konclude_ht::process::node::{IndividualProcessNode, IndividualType};
    use crate::konclude_ht::process::stubs::{
        AdditionalProcessDataAssertionsLinker, AdditionalProcessRoleAssertionsLinker,
        DataAssertionLinkerId, ProcessAssertedDataLiteralLinker,
        ProcessAssertedDataLiteralLinkerId, ReverseRoleAssertionLinkerId, RoleAssertionLinkerId,
    };
    use crate::konclude_ht::process::TrackPointId;

    #[test]
    fn merge_individual_node_into_propagates_invalid_blocking_flag() {
        let mut algo = CompletionTaskHandleAlgorithm::new();
        let mut calc_ctx = CalculationAlgorithmContextBase::new();

        let merge_into = calc_ctx
            .process_context_mut()
            .alloc_node(IndividualProcessNode::new(Id::NONE));
        let individual = calc_ctx
            .process_context_mut()
            .alloc_node(IndividualProcessNode::new(Id::NONE));

        calc_ctx
            .process_context_mut()
            .node_mut(individual)
            .add_processing_restriction_flags(IndividualProcessNode::PRF_INVALIDBLOCKINGORCACHING);
        assert!(!calc_ctx
            .process_context()
            .node(merge_into)
            .has_partial_processing_restriction_flags(
                IndividualProcessNode::PRF_INVALIDBLOCKINGORCACHING,
            ));

        algo.merge_individual_node_into(merge_into, individual, TrackPointId::NONE, &mut calc_ctx);

        assert!(calc_ctx
            .process_context()
            .node(merge_into)
            .has_partial_processing_restriction_flags(
                IndividualProcessNode::PRF_INVALIDBLOCKINGORCACHING,
            ));
    }

    #[test]
    fn merge_individual_node_into_relocates_distinct_edges() {
        let mut algo = CompletionTaskHandleAlgorithm::new();
        let mut calc_ctx = CalculationAlgorithmContextBase::new();

        let merge_into = calc_ctx
            .process_context_mut()
            .alloc_node(IndividualProcessNode::new(Id::NONE));
        let individual = calc_ctx
            .process_context_mut()
            .alloc_node(IndividualProcessNode::new(Id::NONE));
        let other = calc_ctx
            .process_context_mut()
            .alloc_node(IndividualProcessNode::new(Id::NONE));

        calc_ctx
            .process_context_mut()
            .node_mut(merge_into)
            .set_individual_node_id(10);
        calc_ctx
            .process_context_mut()
            .node_mut(individual)
            .set_individual_node_id(20);
        calc_ctx
            .process_context_mut()
            .node_mut(other)
            .set_individual_node_id(30);
        calc_ctx
            .processing_data_box_mut()
            .individual_process_node_vector_mut()
            .set_data(10, merge_into)
            .set_data(20, individual)
            .set_data(30, other);

        let old_dep_track_point = TrackPointId::new(77);
        let mut old_edge = DistinctEdge::new();
        old_edge.init_distinct_edge(individual, other, old_dep_track_point);
        let old_edge = calc_ctx.process_context_mut().alloc_distinct_edge(old_edge);

        let individual_hash = calc_ctx
            .process_context_mut()
            .node_distinct_hash(individual);
        calc_ctx
            .process_context_mut()
            .distinct_hash_mut(individual_hash)
            .insert_distinct_individual(30, old_edge);
        let other_hash = calc_ctx.process_context_mut().node_distinct_hash(other);
        calc_ctx
            .process_context_mut()
            .distinct_hash_mut(other_hash)
            .insert_distinct_individual(20, old_edge);

        algo.merge_individual_node_into(
            merge_into,
            individual,
            TrackPointId::new(88),
            &mut calc_ctx,
        );

        let merge_hash = calc_ctx
            .process_context_mut()
            .node_distinct_hash(merge_into);
        let relocated_edge = calc_ctx
            .process_context()
            .distinct_hash(merge_hash)
            .get_individual_distinct_edge(30);
        assert!(relocated_edge.is_some());
        assert_eq!(
            calc_ctx
                .process_context()
                .distinct_hash(other_hash)
                .get_individual_distinct_edge(20),
            Id::NONE
        );
        assert_eq!(
            calc_ctx
                .process_context()
                .distinct_hash(other_hash)
                .get_individual_distinct_edge(10),
            relocated_edge
        );

        let edge = calc_ctx.process_context().distinct_edge(relocated_edge);
        assert_eq!(edge.get_source_individual(), other);
        assert_eq!(edge.get_destination_individual(), merge_into);
    }

    #[test]
    fn merge_individual_node_into_copies_exact_nominal_connections() {
        let mut algo = CompletionTaskHandleAlgorithm::new();
        algo.conf_exact_nominal_dependency_tracking = true;
        let mut calc_ctx = CalculationAlgorithmContextBase::new();

        let merge_into_nominal = calc_ctx
            .ontology_arenas_mut()
            .alloc_individual(Individual::new(10));
        let individual_nominal = calc_ctx
            .ontology_arenas_mut()
            .alloc_individual(Individual::new(20));

        let merge_into = calc_ctx
            .process_context_mut()
            .alloc_node(IndividualProcessNode::new(Id::NONE));
        let individual = calc_ctx
            .process_context_mut()
            .alloc_node(IndividualProcessNode::new(Id::NONE));

        calc_ctx
            .process_context_mut()
            .node_mut(merge_into)
            .set_individual_node_id(10)
            .set_individual_type(IndividualType::Nominal)
            .set_nominal_individual(merge_into_nominal);
        calc_ctx
            .process_context_mut()
            .node_mut(individual)
            .set_individual_node_id(20)
            .set_individual_type(IndividualType::Nominal)
            .set_nominal_individual(individual_nominal);
        calc_ctx
            .process_context_mut()
            .node_add_successor_connection_to_nominal(individual, -31);
        calc_ctx
            .process_context_mut()
            .node_add_successor_connection_to_nominal(individual, -37);

        algo.merge_individual_node_into(merge_into, individual, TrackPointId::NONE, &mut calc_ctx);

        let mut copied = calc_ctx
            .process_context()
            .node_successor_connected_nominals(merge_into);
        copied.sort_unstable();
        assert_eq!(copied, vec![-37, -31, -20]);
    }

    #[test]
    fn merge_individual_node_into_relocates_assertion_linkers() {
        let mut algo = CompletionTaskHandleAlgorithm::new();
        let mut calc_ctx = CalculationAlgorithmContextBase::new();

        let nominal = calc_ctx
            .ontology_arenas_mut()
            .alloc_individual(Individual::new(10));
        let merge_into = calc_ctx
            .process_context_mut()
            .alloc_node(IndividualProcessNode::new(Id::NONE));
        let individual = calc_ctx
            .process_context_mut()
            .alloc_node(IndividualProcessNode::new(Id::NONE));

        let direct_role = RoleAssertionLinkerId::new(21);
        let direct_reverse = ReverseRoleAssertionLinkerId::new(22);
        let direct_data = DataAssertionLinkerId::new(23);
        let existing_role = RoleAssertionLinkerId::new(31);
        let existing_reverse = ReverseRoleAssertionLinkerId::new(32);
        let existing_data = DataAssertionLinkerId::new(33);
        let existing_role_dep = TrackPointId::new(41);
        let existing_data_dep = TrackPointId::new(42);
        let existing_literal_dep = TrackPointId::new(43);
        let merge_dep = TrackPointId::new(99);

        let mut role_linker = AdditionalProcessRoleAssertionsLinker::new();
        role_linker.init_additional_process_role_assertions_linker(
            101,
            existing_role,
            existing_reverse,
            existing_role_dep,
        );
        let role_linker = calc_ctx
            .process_context_mut()
            .alloc_additional_role_assertion_linker(role_linker);

        let mut data_linker = AdditionalProcessDataAssertionsLinker::new();
        data_linker.init_additional_process_data_assertions_linker(
            102,
            existing_data,
            existing_data_dep,
        );
        let data_linker = calc_ctx
            .process_context_mut()
            .alloc_additional_data_assertion_linker(data_linker);

        let mut literal_linker = ProcessAssertedDataLiteralLinker::new();
        literal_linker.init_process_data_literal_linker(700, existing_literal_dep);
        let literal_linker = calc_ctx
            .process_context_mut()
            .alloc_process_asserted_data_literal_linker(literal_linker);

        calc_ctx
            .process_context_mut()
            .node_mut(individual)
            .set_nominal_individual(nominal)
            .set_assertion_role_linker(direct_role)
            .set_reverse_assertion_role_linker(direct_reverse)
            .set_assertion_data_linker(direct_data)
            .set_additional_role_assertions_linker(role_linker)
            .set_additional_data_assertions_linker(data_linker)
            .set_asserted_data_literal_linker(literal_linker)
            .add_initializing_concept_linker(vec![
                NegLink {
                    target: ConceptId::new(1),
                    negated: false,
                },
                NegLink {
                    target: ConceptId::new(2),
                    negated: true,
                },
            ]);

        algo.merge_individual_node_into(merge_into, individual, merge_dep, &mut calc_ctx);

        let role_head = calc_ctx
            .process_context()
            .node(merge_into)
            .additional_role_assertions_linker();
        let cloned_role = calc_ctx
            .process_context()
            .additional_role_assertion_linker(role_head);
        assert_eq!(cloned_role.individual(), 101);
        assert_eq!(cloned_role.role_assertion_linker(), existing_role);
        assert_eq!(
            cloned_role.reverse_role_assertion_linker(),
            existing_reverse
        );
        let direct_role_head = cloned_role.next();
        let direct_role_entry = calc_ctx
            .process_context()
            .additional_role_assertion_linker(direct_role_head);
        assert_eq!(direct_role_entry.individual(), nominal.raw);
        assert_eq!(direct_role_entry.role_assertion_linker(), direct_role);
        assert_eq!(
            direct_role_entry.reverse_role_assertion_linker(),
            direct_reverse
        );
        assert_eq!(direct_role_entry.dependency_track_point(), merge_dep);

        let init = calc_ctx
            .process_context()
            .node(merge_into)
            .initializing_concept_linker();
        assert_eq!(init.len(), 2);
        assert_eq!(init[0].target, ConceptId::new(2));
        assert!(init[0].negated);
        assert_eq!(init[1].target, ConceptId::new(1));
        assert!(!init[1].negated);

        let data_head = calc_ctx
            .process_context()
            .node(merge_into)
            .additional_data_assertions_linker();
        let cloned_data = calc_ctx
            .process_context()
            .additional_data_assertion_linker(data_head);
        assert_eq!(cloned_data.individual(), 102);
        assert_eq!(cloned_data.data_assertion_linker(), existing_data);
        let direct_data_head = cloned_data.next();
        let direct_data_entry = calc_ctx
            .process_context()
            .additional_data_assertion_linker(direct_data_head);
        assert_eq!(direct_data_entry.individual(), nominal.raw);
        assert_eq!(direct_data_entry.data_assertion_linker(), direct_data);
        assert_eq!(direct_data_entry.dependency_track_point(), merge_dep);

        let literal_head = calc_ctx
            .process_context()
            .node(merge_into)
            .asserted_data_literal_linker();
        let literal = calc_ctx
            .process_context()
            .process_asserted_data_literal_linker(literal_head);
        assert_eq!(literal.data_literal(), 700);
        assert_eq!(literal.next(), ProcessAssertedDataLiteralLinkerId::NONE);
    }

    #[test]
    fn merge_individual_node_into_transfers_value_backed_role_assertions() {
        let mut algo = CompletionTaskHandleAlgorithm::new();
        let mut calc_ctx = CalculationAlgorithmContextBase::new();
        let role = calc_ctx.ontology_arenas_mut().alloc_role(Role::new());
        let merge_into_individual = calc_ctx
            .ontology_arenas_mut()
            .alloc_individual(Individual::new(10));
        let merged_individual = calc_ctx
            .ontology_arenas_mut()
            .alloc_individual(Individual::new(20));
        let forward_target_individual = calc_ctx
            .ontology_arenas_mut()
            .alloc_individual(Individual::new(30));
        let reverse_source_individual = calc_ctx
            .ontology_arenas_mut()
            .alloc_individual(Individual::new(40));

        let mut allocate_nominal =
            |individual, tag: i64, calc_ctx: &mut CalculationAlgorithmContextBase| {
                let node = calc_ctx
                    .process_context_mut()
                    .alloc_node(IndividualProcessNode::new(Id::NONE));
                calc_ctx
                    .process_context_mut()
                    .node_mut(node)
                    .set_individual_node_id(-tag)
                    .set_individual_type(IndividualType::Nominal)
                    .set_nominal_individual(individual);
                calc_ctx
                    .processing_data_box_mut()
                    .individual_process_node_vector_mut()
                    .set_data(-tag, node);
                node
            };
        let merge_into = allocate_nominal(merge_into_individual, 10, &mut calc_ctx);
        let merged = allocate_nominal(merged_individual, 20, &mut calc_ctx);
        let forward_target = allocate_nominal(forward_target_individual, 30, &mut calc_ctx);
        let reverse_source = allocate_nominal(reverse_source_individual, 40, &mut calc_ctx);
        let forward = RoleAssertion {
            role,
            individual: forward_target_individual,
        };
        let reverse = ReverseRoleAssertion {
            individual: reverse_source_individual,
            role,
            role_assertion: role.raw,
        };
        calc_ctx
            .process_context_mut()
            .node_mut(merged)
            .set_assertion_role_assertions(vec![forward])
            .set_reverse_assertion_role_assertions(vec![reverse]);

        let merge_dependency = calc_ctx.get_or_create_base_dependency_track_point();
        algo.merge_individual_node_into(merge_into, merged, merge_dependency, &mut calc_ctx);
        let survivor = calc_ctx.process_context().node(merge_into);
        assert!(survivor.assertion_role_assertions().contains(&forward));
        assert!(survivor
            .reverse_assertion_role_assertions()
            .contains(&reverse));
        assert!(algo
            .ht_role_successor_links(merge_into, role, &calc_ctx)
            .iter()
            .any(|&(_, successor)| successor == forward_target));
        assert!(algo
            .ht_role_successor_links(reverse_source, role, &calc_ctx)
            .iter()
            .any(|&(_, successor)| successor == merge_into));
    }
}
