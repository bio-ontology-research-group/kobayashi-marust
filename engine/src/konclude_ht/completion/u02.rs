//! `completion::u02` — port unit #2 of the completion task-handle algorithm
//! (Core processing loop / driver family).
//!
//! Ports three methods of Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.cpp`:
//!   - `continueIndividualProcessing`   (.cpp 2074–2094)
//!   - `takeNextProcessIndividual`      (.cpp 2190–2790)
//!   - `analyzeCompletionGraphStatistics` (.cpp 2794–2825)
//!
//! KONCLUDE-PORT-NOTE[ownership]: C++ threads the per-thread
//! `CCalculationAlgorithmContextBase*` through every method; the port passes it as
//! an explicit `&CalculationAlgorithmContextBase` / `&mut CalculationAlgorithmContextBase`
//! parameter (it owns the single `ProcessingDataBox`). `CIndividualProcessNode*`
//! becomes a `NodeId` (arena index). Individual nodes are resolved through the
//! not-yet-ported `getLocalizedIndividual`/node-arena subsystem, so the node-flag
//! and label-set reads below are `W3-DEFER[api]` stubs while the control flow is
//! kept verbatim.

#![allow(dead_code, unused_variables, unused_mut)]

use super::super::model::substrate::Cint64;
use super::super::model::ConceptId;
use super::super::process::node::IndividualProcessNode;
use super::super::process::queues::{ConceptProcessingQueue, ConceptProcessingQueueId};
use super::super::process::{ConDescId, LabelSetId, NodeId, TrackPointId};
use super::algorithm::{IndiNodeQueueType, DETERMINISTIC_PROCESS_PRIORITY};
use super::clash::CalcSignal;
use super::context::CalculationAlgorithmContextBase;

impl super::algorithm::CompletionTaskHandleAlgorithm {
    fn take_next_backend_reuse_expansion_individual(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        let q = calc_alg_context.get_backend_individual_reuse_expansion_queue(false);
        if q.is_some()
            && !calc_alg_context
                .process_context()
                .indi_unsorted_proc_queue(q)
                .is_empty()
        {
            let q = calc_alg_context.get_backend_individual_reuse_expansion_queue(true);
            let indi_proc_node = calc_alg_context
                .process_context_mut()
                .indi_unsorted_proc_queue_mut(q)
                .take_next_process_individual_node();
            self.indi_node_from_queue_type = IndiNodeQueueType::Inqt_BackendExpansionReuse;
            return indi_proc_node;
        }
        NodeId::NONE
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::continueIndividualProcessing`.
    pub fn continue_individual_processing(
        &self,
        indi_proc_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // bool purgedIndiBlocked = indiProcNode->hasIndirectBlockedProcessingRestrictionFlags()
        //                          || indiProcNode->hasPurgedBlockedProcessingRestrictionFlags();
        let purged_indi_blocked = {
            let node = calc_alg_context.process_context().node(indi_proc_node);
            node.has_indirect_blocked_processing_restriction_flags()
                || node.has_purged_blocked_processing_restriction_flags()
        };
        if purged_indi_blocked {
            return false;
        }

        // CConceptProcessingQueue* conProQue = indiProcNode->getConceptProcessingQueue(false);
        let con_pro_que: ConceptProcessingQueueId = calc_alg_context
            .process_context_mut()
            .node_concept_processing_queue(indi_proc_node, false);

        // if (conProQue && !conProQue->isEmpty()) {
        if con_pro_que.is_some()
            && !calc_alg_context
                .process_context()
                .concept_proc_queue(con_pro_que)
                .is_empty()
        {
            // CConceptProcessPriority conProPri;
            // if (conProQue->getNextConceptProcessPriority(&conProPri)) {
            if let Some(con_pro_pri) = ConceptProcessingQueue::get_next_concept_process_priority(
                con_pro_que,
                calc_alg_context.process_context_mut(),
            ) {
                // double priority = conProPri.getPriority();
                let priority: f64 = con_pro_pri.get_priority();
                if priority < self.min_concept_processing_priority_level {
                    return false;
                }
            }
            return true;
        }
        false
    }

    /// W8: a thin standalone drive entry the selftest harness (and any non-Task
    /// caller) can invoke WITHOUT the still-`W3-DEFER` Task / scheduler adapter that
    /// `handle_task` acquires (`handle_task` short-circuits on
    /// `sat_calc_task == Id::NONE`). It performs `handle_task`'s inner main loop
    /// directly on a constructed context (cpp 1112-1236):
    ///
    /// ```text
    /// indi = takeNextProcessIndividual(ctx)
    /// while indi && !clash:
    ///   if individualNodeInitializing(indi, ctx):
    ///     cont = continueIndividualProcessing(indi, ctx)
    ///     while cont && !clash:
    ///       q = indi.getConceptProcessingQueue(true)
    ///       cpd = q.takeNextConceptDescriptorProcess()
    ///       cont = tableauRuleProcessing(indi, cpd, ctx)   // → tableauRuleChoice → apply_*_rule
    ///       if cont: cont = continueIndividualProcessing(indi, ctx)
    ///       else:    addConceptToProcessingQueue(cpd, q, indi, ctx)   // reinsert
    ///     individualNodeConclusion(indi, ctx)
    ///   indi = takeNextProcessIndividual(ctx)
    /// ```
    ///
    /// A raised clash/stop signal (the `clash.rs` stand-in for the C++
    /// `throw CCalculationClashProcessingException`, which `handle_task` catches)
    /// ends the drive early. Returns `true` if the completion graph is CONSISTENT
    /// (no clash raised), `false` if a clash/stop fired — exactly the verdict
    /// `handle_task`'s catch reads off the pending signal.
    ///
    /// The seeded root node must already be ON one of the individual processing
    /// queues (e.g. the immediately-processing queue) so `take_next_process_individual`
    /// returns it; that is the `buildCompletionGraph` seed the caller performs.
    pub fn run_completion_on(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // The outer search loop. `run_saturation_loop` drives the deterministic
        // completion until it either reaches a fixpoint (no pending signal ⇒
        // CONSISTENT) or a rule raises a clash/stop. On a clash with an open
        // disjunction branch point, `try_backtrack_or_branch` restores to the topmost
        // branch with a remaining alternative, clears the clash, and adds the next
        // disjunct; the loop then re-drives. When no open branch remains the clash is
        // genuine ⇒ INCONSISTENT. (Konclude does this with per-alternative task forks +
        // `clashedBacktracking`; see the `OrBranchPoint` KONCLUDE-PORT-NOTE.)
        loop {
            self.run_saturation_loop(calc_alg_context);
            if !calc_alg_context.has_pending_signal() {
                // fixpoint reached, no clash ⇒ consistent / complete.
                return true;
            }
            match calc_alg_context.pending_signal() {
                CalcSignal::Clash(_) => {
                    if self.try_backtrack_or_branch(calc_alg_context) {
                        // advanced to the next alternative (signal cleared); re-drive.
                        continue;
                    }
                    // no open branch point with a remaining alternative ⇒ the clash is
                    // unrecoverable: the completion graph is INCONSISTENT.
                    return false;
                }
                // a stop is the C++ `CCalculationStopProcessingException` (task forked
                // / completed elsewhere); not consistent on this drive.
                CalcSignal::Stop { .. } => return false,
                CalcSignal::Continue => return true,
            }
        }
    }

    /// The in-process disjunction backtrack. Pops branch points whose alternatives
    /// are all exhausted, then — if any open branch remains — restores to the topmost
    /// one, clears the pending clash, advances to its next unexplored disjunct, adds
    /// it to the individual, and re-seeds the node onto the immediately-processing
    /// queue so the drive picks it up again. Returns true if it advanced a branch,
    /// false if no branch with a remaining alternative exists (the clash is genuine).
    ///
    /// KONCLUDE-PORT-NOTE[branching]: this is a CHRONOLOGICAL backtrack — it relies on
    /// the failed alternative having committed no graph mutation that needs undoing,
    /// which holds when the disjunct clashes at insert-time (`A` added while `¬A`
    /// present: the polarity clash fires in `insert_concept_get_clash_resolved`
    /// BEFORE the concept enters the label set, so the set is unchanged). The faithful
    /// dependency-directed backjump (`clashedBacktracking`, u29) with full arena /
    /// databox watermark restore (the Arena `truncate_to` + db1 save/restore) is the
    /// documented gap — it needs the unported Unit 28/30 tracking-line records.
    fn try_backtrack_or_branch(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // discard branch points whose every alternative has already clashed.
        while let Some(bp) = self.or_branch_stack.last() {
            if bp.next_alt < bp.disjuncts.len() {
                break;
            }
            self.or_branch_stack.pop();
        }
        if self.or_branch_stack.is_empty() {
            return false;
        }

        // the clash is being recovered from — clear it (the C++ catch consumes the
        // exception, then `clashedBacktracking` re-drives the chosen branch).
        calc_alg_context.clear_pending_signal();

        // advance the topmost open branch to its next unexplored alternative.
        let (node, target, op_negated, dep_track_point) = {
            let bp = self.or_branch_stack.last_mut().expect("checked non-empty");
            let link = bp.disjuncts[bp.next_alt];
            bp.next_alt += 1;
            (
                bp.node,
                link.target,
                link.negated ^ bp.negate,
                bp.dep_track_point,
            )
        };

        // re-seed the node onto the immediately-processing queue so
        // `take_next_process_individual` (Probe 2) returns it on the next drive.
        let iq = calc_alg_context.get_individual_immediately_processing_queue(true);
        calc_alg_context
            .process_context_mut()
            .indi_unsorted_proc_queue_mut(iq)
            .insert_indiviudal_process_node(node);

        // addConceptToIndividual(nextOperand, opNegated, node, depTrackPoint, …) — the
        // `executeORBranching` per-alternative add. May itself raise a clash (the
        // alternative also contradicts the label set), which the outer loop catches
        // and backtracks again.
        let mut node_m: NodeId = node;
        let _target: ConceptId = target;
        self.add_concept_to_individual(
            target,
            op_negated,
            &mut node_m,
            dep_track_point,
            true,
            true,
            calc_alg_context,
        );
        true
    }

    /// The deterministic completion main loop (`handleTask` inner loop, cpp
    /// 1112-1236), factored out of [`Self::run_completion_on`] so the outer search
    /// loop can re-enter it after a disjunction backtrack. Drives until the
    /// completion graph is saturated OR a rule raises a pending clash/stop signal
    /// (which it leaves set for the caller to inspect); it does not itself decide
    /// the verdict.
    fn run_saturation_loop(&mut self, calc_alg_context: &mut CalculationAlgorithmContextBase) {
        if calc_alg_context.has_pending_signal() {
            return;
        }
        // KONCLUDE-PORT-NOTE[W16-successor-drain]: hard iteration cap — a safety net so a
        // regression that generates successors without a terminating guard (blocking is a
        // later wave) cannot HANG the build host. Set far above any real test workload; in
        // normal operation it is never reached. On overrun we raise a stop (the drive ends
        // "not consistent" rather than silently claiming consistency).
        const MAX_DRIVE_ITERATIONS: u64 = 5_000_000;
        let mut drive_iters: u64 = 0;
        let mut indi_proc_node: NodeId = self.take_next_process_individual(calc_alg_context);
        if calc_alg_context.has_pending_signal() {
            return;
        }
        while indi_proc_node.is_some() {
            drive_iters += 1;
            if drive_iters > MAX_DRIVE_ITERATIONS {
                calc_alg_context.raise_stop(false);
                return;
            }
            let initialized = self.individual_node_initializing(indi_proc_node, calc_alg_context);
            if calc_alg_context.has_pending_signal() {
                return;
            }
            if initialized {
                let mut continue_processing_individual =
                    self.continue_individual_processing(indi_proc_node, calc_alg_context);
                if calc_alg_context.has_pending_signal() {
                    return;
                }
                while continue_processing_individual {
                    drive_iters += 1;
                    if drive_iters > MAX_DRIVE_ITERATIONS {
                        calc_alg_context.raise_stop(false);
                        return;
                    }
                    // CConceptProcessingQueue* conProcQueue = indiProcNode->getConceptProcessingQueue(true);
                    let con_proc_queue: ConceptProcessingQueueId = calc_alg_context
                        .process_context_mut()
                        .node_concept_processing_queue(indi_proc_node, true);
                    // conProcDes = conProcQueue->takeNextConceptDescriptorProcess();
                    let con_proc_des = ConceptProcessingQueue::take_next_concept_descriptor_process(
                        con_proc_queue,
                        calc_alg_context.process_context_mut(),
                    );

                    self.current_rec_proc_depth = 0;
                    self.applied_total_rule_count += 1;

                    // tableauRuleProcessing → tableauRuleChoice → apply_*_rule engine.
                    continue_processing_individual = self.tableau_rule_processing(
                        indi_proc_node,
                        con_proc_des,
                        calc_alg_context,
                    );
                    // The clash/stop a rule may raise unwinds HERE (the C++ throw from
                    // inside tableauRuleProcessing), before the reinsert/continue branch.
                    if calc_alg_context.has_pending_signal() {
                        return;
                    }

                    if continue_processing_individual {
                        continue_processing_individual =
                            self.continue_individual_processing(indi_proc_node, calc_alg_context);
                        if calc_alg_context.has_pending_signal() {
                            return;
                        }
                    } else {
                        self.add_concept_to_processing_queue_reinsert(
                            con_proc_des,
                            con_proc_queue,
                            indi_proc_node,
                            calc_alg_context,
                        );
                        if calc_alg_context.has_pending_signal() {
                            return;
                        }
                    }
                }

                self.individual_node_conclusion(indi_proc_node, calc_alg_context);
                if calc_alg_context.has_pending_signal() {
                    return;
                }
            }

            indi_proc_node = self.take_next_process_individual(calc_alg_context);
            if calc_alg_context.has_pending_signal() {
                return;
            }
        }
    }

    /// Shared body for the early/late `CIndividualReactivationProcessingQueue`
    /// probes in `takeNextProcessIndividual`.
    fn take_next_reactivation_individual_from_queue(
        &mut self,
        q: super::super::process::queues::IndividualReactivationProcessingQueueId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        let (react_indi_node, force_reactivation) = calc_alg_context
            .process_context_mut()
            .indi_reactivation_proc_queue_mut(q)
            .take_next_reactivation_individual()
            .unwrap_or((NodeId::NONE, false));
        let indi_proc_node = self.get_localized_individual(react_indi_node, true, calc_alg_context);
        if force_reactivation {
            let completion_graph_cached = calc_alg_context
                .process_context()
                .node(indi_proc_node)
                .has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_COMPLETIONGRAPHCACHED,
                );
            if completion_graph_cached {
                calc_alg_context
                    .process_context_mut()
                    .node_mut(indi_proc_node)
                    .clear_processing_restriction_flags(
                        IndividualProcessNode::PRF_COMPLETIONGRAPHCACHED,
                    );
                self.reapply_satisfiable_cached_absorbed_disjunction_concepts(
                    indi_proc_node,
                    calc_alg_context,
                );
                self.reapply_satisfiable_cached_absorbed_generating_concepts(
                    indi_proc_node,
                    calc_alg_context,
                );
            }
            calc_alg_context
                .process_context_mut()
                .node_mut(indi_proc_node)
                .add_processing_restriction_flags(
                    IndividualProcessNode::PRF_COMPLETIONGRAPHCACHINGINVALIDATED,
                );
        }
        indi_proc_node
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::takeNextProcessIndividual`.
    ///
    /// PORT-PENDING: the 601-line body probes ~40 distinct processing queues /
    /// review sets in a fixed priority order, none of whose container subsystems are
    /// ported yet (the Process-layer processing queues, the `IndividualProcessNodeVector`,
    /// the backend-neighbour-expansion controlling data, the signature-blocking /
    /// reusing review data, the nominal-non-deterministic sort linkers), and it
    /// dispatches into ~30 not-yet-ported algorithm helpers from other units
    /// (`getLocalizedIndividual`, `getUpToDateIndividual`,
    /// `queuedIndividualBackendNeighbourExpansion`,
    /// `detectIndividualNodeSignatureBlockingStatus`, `expand*FromBackendCache`,
    /// `reuseIndividualBackendExpansion`, `incrementalNodeExpansion`,
    /// `incrementalMergeWithPreviousDeterministicCompletionGraph`,
    /// `getCorrectedNominalIndividualNode`, ...). The signature is preserved; the
    /// fixed probe order is recorded for the eventual full port.
    ///
    /// Probe order (each guarded by `if (!indiProcNode)`, setting mIndiNodeFromQueueType):
    ///   1. cache-testing nodes                  (INQT_CACHETEST, sets concludeUnsatCaching)
    ///   2. immediately-processing queue         (INQT_IMMEDIATE)
    ///   3. delayed-backend-init queue           (INQT_DELAYEDBACKENDINIT)
    ///   4. role-assertion-expansion queue       (INQT_ROLEASS)
    ///   5. depth-deterministic-expansion queue  (INQT_DETEXP, min-pri=deterministic)
    ///   6. depth-first-deterministic-exp queue  (INQT_DEPTHFIRST)
    ///   7. distinct value-space sat-checking    (INQT_VSTSATTESTING)
    ///   8. value-space-triggering queue         (INQT_VSTRIGGERING)
    ///   9. backend-cache-sync retest queue      (INQT_BACKENDSYNCRETEST)
    ///  10. backend-direct-influence-expansion   (INQT_BACKENDDIRECTINFLUENCEEXPANSION)
    ///  11. variable-binding concept batch queue (INQT_VARBINDBATCHQUE)
    ///  12. incremental-compatibility checking   (drains, checkCompatibilityUpdate...)
    ///  13. incremental-expansion initializing   (drains, initializeIncremental...)
    ///  14. incremental-expansion queue          (incrementalNodeExpansion)
    ///  15. incremental compatible-merge         (incrementalMergeWithPreviousDeterministic...)
    ///  16. early individual-reactivation queue  (INQT_COMPCACHEDREACT)
    ///  17. sort nominal-non-deterministic nodes (qSort by id desc)
    ///  18. prepare backend-expansion-reuse branching
    ///  19. fixed-mode backend reuse-expansion   (INQT_BACKENDEXPANSIONREUSE)
    ///  20. individual processing queue          (INQT_OUTDATED, min-pri=0)
    ///  21. nominal processing queue             (INQT_NOMINAL)
    ///  22. backend individual neighbour expansion
    ///  23. propagation-cut backend expansion    (recurse into takeNextProcessIndividual)
    ///  24. sorted nominal-non-deterministic node (INQT_NOMINAL)
    ///  25. individual depth processing queue    (INQT_DEPTHNORMAL)
    ///  26. nominal-caching-loss reactivation     (INQT_NOMINALCACHINGLOSSREACTIVATION)
    ///  27. individual depth-first queue          (INQT_DEPTHFIRST)
    ///  28. late individual-reactivation queue    (INQT_COMPCACHEDREACT)
    ///  29. blocking-update review queue          (INQT_BLOCKUP)
    ///  30. blocked-reactivation queue            (INQT_BLOCKREACT)
    ///  31. signature-blocking review set
    ///  32. reusing review data
    ///  33. backend late neighbour expansion
    ///  34. prioritized-mode backend reuse-expansion (INQT_BACKENDEXPANSIONREUSE)
    ///  35. delaying-nominal processing queue     (INQT_DELAYEDNOMINAL)
    ///  36. backend indirect-compatibility expansion (INQT_BACKENDINDIRECTCOMPATIBILITYEXPANSION)
    pub fn take_next_process_individual(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        // CIndividualProcessNode* indiProcNode = nullptr;
        let mut indi_proc_node: NodeId = NodeId::NONE;
        // mIndiNodeConcludeUnsatCaching = false;
        self.indi_node_conclude_unsat_caching = false;
        // mIndiNodeFromQueueType = INQT_NONE;
        self.indi_node_from_queue_type = IndiNodeQueueType::Inqt_None;

        // --- Probe 1: cache-testing individual nodes (cpp 2195-2202). LIVE. ---
        // This arm is backed by the real `mIndividualNodeCacheTestingLinker`
        // (`process/db4.rs`), so it is ported in full.
        if indi_proc_node.is_none() {
            // mMinConceptProcessingPriorityLevel = mImmediatelyProcessPriority;
            self.min_concept_processing_priority_level =
                super::algorithm::IMMEDIATELY_PROCESS_PRIORITY as f64;
            if calc_alg_context
                .processing_data_box()
                .has_cache_testing_individual_nodes()
            {
                indi_proc_node = calc_alg_context
                    .processing_data_box_mut()
                    .take_next_cache_testing_individual_node();
                self.indi_node_conclude_unsat_caching = true;
                self.indi_node_from_queue_type = IndiNodeQueueType::Inqt_CacheTest;
            }
        }

        // --- Probe 2: immediately-processing queue (cpp 2204-2210). LIVE. ---
        if indi_proc_node.is_none() {
            let q = calc_alg_context.get_individual_immediately_processing_queue(false);
            if q.is_some()
                && !calc_alg_context
                    .process_context()
                    .indi_unsorted_proc_queue(q)
                    .is_empty()
            {
                let q = calc_alg_context.get_individual_immediately_processing_queue(true);
                indi_proc_node = calc_alg_context
                    .process_context_mut()
                    .indi_unsorted_proc_queue_mut(q)
                    .take_next_process_individual_node();
                self.indi_node_from_queue_type = IndiNodeQueueType::Inqt_Immediate;
            }
        }

        // --- Probe 3: delayed-backend-init queue (cpp 2212-2226). W3-DEFER[api]:
        // `CIndividualDelayedBackendInitializationProcessingQueue` stub +
        // `getUpToDateIndividual` MISS path + backend-sync data. ---

        // --- Probe 4: role-assertion-expansion queue (cpp 2228-2234). LIVE. ---
        if indi_proc_node.is_none() {
            let q = calc_alg_context.get_role_assertion_expansion_processing_queue(false);
            if q.is_some()
                && !calc_alg_context
                    .process_context()
                    .indi_unsorted_proc_queue(q)
                    .is_empty()
            {
                let q = calc_alg_context.get_role_assertion_expansion_processing_queue(true);
                indi_proc_node = calc_alg_context
                    .process_context_mut()
                    .indi_unsorted_proc_queue_mut(q)
                    .take_next_process_individual_node();
                self.indi_node_from_queue_type = IndiNodeQueueType::Inqt_RoleAss;
            }
        }

        // --- Probe 5: depth-deterministic-expansion preprocessing queue
        // (cpp 2236-2243, min-pri = deterministic). LIVE. ---
        if indi_proc_node.is_none() {
            self.min_concept_processing_priority_level = DETERMINISTIC_PROCESS_PRIORITY as f64;
            let q = calc_alg_context
                .get_individual_depth_deterministic_expansion_preprocessing_queue(false);
            if q.is_some()
                && !calc_alg_context
                    .process_context()
                    .indi_depth_proc_queue(q)
                    .is_empty()
            {
                let q = calc_alg_context
                    .get_individual_depth_deterministic_expansion_preprocessing_queue(true);
                indi_proc_node = calc_alg_context
                    .process_context_mut()
                    .indi_depth_queue_take_next(q);
                self.indi_node_from_queue_type = IndiNodeQueueType::Inqt_DetExp;
            }
        }

        // --- Probe 6: depth-first-deterministic-exp queue (cpp 2245-2251). LIVE. ---
        if indi_proc_node.is_none() {
            let q = calc_alg_context
                .get_individual_depth_first_deterministic_expansion_processing_queue(false);
            if q.is_some()
                && !calc_alg_context
                    .process_context()
                    .indi_unsorted_proc_queue(q)
                    .is_empty()
            {
                let q = calc_alg_context
                    .get_individual_depth_first_deterministic_expansion_processing_queue(true);
                indi_proc_node = calc_alg_context
                    .process_context_mut()
                    .indi_unsorted_proc_queue_mut(q)
                    .take_next_process_individual_node();
                self.indi_node_from_queue_type = IndiNodeQueueType::Inqt_DepthFirst;
            }
        }

        // --- Probe 7: distinct value-space sat-checking queue (cpp 2259-2270). LIVE. ---
        if indi_proc_node.is_none() {
            let q = calc_alg_context.get_distinct_value_space_satisfiability_checking_queue(false);
            if q.is_some()
                && !calc_alg_context
                    .process_context()
                    .indi_depth_proc_queue(q)
                    .is_empty()
            {
                let q =
                    calc_alg_context.get_distinct_value_space_satisfiability_checking_queue(true);
                indi_proc_node = calc_alg_context
                    .process_context_mut()
                    .indi_depth_queue_take_next(q);
                self.indi_node_from_queue_type = IndiNodeQueueType::Inqt_VstSatTesting;
                if indi_proc_node.is_some() {
                    indi_proc_node =
                        calc_alg_context.get_localized_individual(indi_proc_node, true);
                }
            }
        }

        // --- Probe 8: value-space-triggering queue (cpp 2272-2283). LIVE. ---
        if indi_proc_node.is_none() {
            let q = calc_alg_context.get_value_space_triggering_processing_queue(false);
            if q.is_some()
                && !calc_alg_context
                    .process_context()
                    .indi_depth_proc_queue(q)
                    .is_empty()
            {
                let q = calc_alg_context.get_value_space_triggering_processing_queue(true);
                indi_proc_node = calc_alg_context
                    .process_context_mut()
                    .indi_depth_queue_take_next(q);
                self.indi_node_from_queue_type = IndiNodeQueueType::Inqt_VsTriggering;
                if indi_proc_node.is_some() {
                    indi_proc_node =
                        calc_alg_context.get_localized_individual(indi_proc_node, true);
                }
            }
        }

        // --- Probe 9: backend-cache-sync retest queue (cpp 2287-2293). LIVE. ---
        if indi_proc_node.is_none() {
            let q = calc_alg_context.get_backend_cache_synchronization_processing_queue(false);
            if q.is_some()
                && !calc_alg_context
                    .process_context()
                    .indi_unsorted_proc_queue(q)
                    .is_empty()
            {
                let q = calc_alg_context.get_backend_cache_synchronization_processing_queue(true);
                indi_proc_node = calc_alg_context
                    .process_context_mut()
                    .indi_unsorted_proc_queue_mut(q)
                    .take_next_process_individual_node();
                self.indi_node_from_queue_type = IndiNodeQueueType::Inqt_BackendSyncRetest;
            }
        }

        // --- Probe 10: backend-direct-influence-expansion queue (cpp 2295-2301). LIVE. ---
        if indi_proc_node.is_none() {
            let q = calc_alg_context.get_backend_direct_influence_expansion_queue(false);
            if q.is_some()
                && !calc_alg_context
                    .process_context()
                    .indi_unsorted_proc_queue(q)
                    .is_empty()
            {
                let q = calc_alg_context.get_backend_direct_influence_expansion_queue(true);
                indi_proc_node = calc_alg_context
                    .process_context_mut()
                    .indi_unsorted_proc_queue_mut(q)
                    .take_next_process_individual_node();
                self.indi_node_from_queue_type =
                    IndiNodeQueueType::Inqt_BackendDirectInfluenceExpansion;
            }
        }

        // --- Probe 11: variable-binding concept-batch (cpp 2305-2315). LIVE. ---
        if indi_proc_node.is_none() {
            let q = calc_alg_context.get_variable_binding_concept_batch_processing_queue(false);
            if q.is_some()
                && !calc_alg_context
                    .process_context()
                    .indi_concept_batch_proc_queue(q)
                    .is_empty()
            {
                let q = calc_alg_context.get_variable_binding_concept_batch_processing_queue(true);
                let next =
                    calc_alg_context.take_next_variable_binding_concept_batch_process_individual(q);
                if let Some((_var_bind_concept, batch_indi_node, con_pro_des)) = next {
                    if batch_indi_node.is_some() {
                        let localized =
                            self.get_localized_individual(batch_indi_node, true, calc_alg_context);
                        let con_pro_que = calc_alg_context
                            .process_context_mut()
                            .node_concept_processing_queue(localized, true);
                        ConceptProcessingQueue::insert_concept_process_descriptor(
                            con_pro_que,
                            con_pro_des,
                            calc_alg_context.process_context_mut(),
                        );
                        indi_proc_node = localized;
                        self.indi_node_from_queue_type = IndiNodeQueueType::Inqt_VarBindBatchQue;
                    }
                }
            }
        }

        // --- Probe 12: incremental compatibility-checking queue (cpp 2318-2337). LIVE. ---
        if indi_proc_node.is_none() {
            let q = calc_alg_context.get_incremental_compatibility_checking_queue(false);
            if q.is_some()
                && !calc_alg_context
                    .process_context()
                    .indi_depth_proc_queue(q)
                    .is_empty()
            {
                let q = calc_alg_context.get_incremental_compatibility_checking_queue(true);
                while !calc_alg_context
                    .process_context()
                    .indi_depth_proc_queue(q)
                    .is_empty()
                {
                    let mut comp_check_indi_node = calc_alg_context
                        .process_context_mut()
                        .indi_depth_queue_take_next(q);
                    comp_check_indi_node =
                        self.get_localized_individual(comp_check_indi_node, true, calc_alg_context);
                    calc_alg_context
                        .process_context_mut()
                        .node_mut(comp_check_indi_node)
                        .set_incremental_compatibility_checking_queued(false);
                    if calc_alg_context
                        .process_context()
                        .node(comp_check_indi_node)
                        .has_partial_processing_restriction_flags(
                            IndividualProcessNode::PRF_INCREMENTALEXPANSIONRETESTDUEDIRECTMODIFIED,
                        )
                    {
                        calc_alg_context
                            .process_context_mut()
                            .node_mut(comp_check_indi_node)
                            .clear_processing_restriction_flags(
                                IndividualProcessNode::PRF_INCREMENTALEXPANSIONRETESTDUEDIRECTMODIFIED,
                            );
                    }
                    self.check_compatibility_update_directly_changed_propagation(
                        comp_check_indi_node,
                        calc_alg_context,
                    );
                }
            }
        }

        // --- Probe 13: incremental-expansion initializing queue (cpp 2340-2361). LIVE. ---
        if indi_proc_node.is_none() {
            let q = calc_alg_context.get_incremental_expansion_initializing_processing_queue(false);
            if q.is_some()
                && !calc_alg_context
                    .process_context()
                    .indi_depth_proc_queue(q)
                    .is_empty()
            {
                let q =
                    calc_alg_context.get_incremental_expansion_initializing_processing_queue(true);
                while !calc_alg_context
                    .process_context()
                    .indi_depth_proc_queue(q)
                    .is_empty()
                {
                    let mut inc_exp_init_indi_node = calc_alg_context
                        .process_context_mut()
                        .indi_depth_queue_take_next(q);
                    inc_exp_init_indi_node = self.get_localized_individual(
                        inc_exp_init_indi_node,
                        true,
                        calc_alg_context,
                    );
                    calc_alg_context
                        .process_context_mut()
                        .node_mut(inc_exp_init_indi_node)
                        .set_incremental_expansion_queued(false);
                    if self.requires_incremental_node_expansion(
                        inc_exp_init_indi_node,
                        calc_alg_context,
                    ) {
                        self.initialize_incremental_individual_expansion(
                            inc_exp_init_indi_node,
                            calc_alg_context,
                        );
                    }
                }
            }
        }

        // --- Probe 14: incremental-expansion processing queue (cpp 2364-2373). LIVE. ---
        if indi_proc_node.is_none() {
            let q = calc_alg_context.get_incremental_expansion_processing_queue(false);
            if q.is_some()
                && !calc_alg_context
                    .process_context()
                    .indi_custom_priority_proc_queue(q)
                    .is_empty()
            {
                let q = calc_alg_context.get_incremental_expansion_processing_queue(true);
                while indi_proc_node.is_none()
                    && !calc_alg_context
                        .process_context()
                        .indi_custom_priority_proc_queue(q)
                        .is_empty()
                {
                    let mut inc_exp_indi_node = calc_alg_context
                        .process_context_mut()
                        .indi_custom_priority_queue_take_next(q);
                    inc_exp_indi_node =
                        self.get_localized_individual(inc_exp_indi_node, true, calc_alg_context);
                    calc_alg_context
                        .process_context_mut()
                        .node_mut(inc_exp_indi_node)
                        .set_incremental_expansion_queued(false);
                    if self.requires_incremental_node_expansion(inc_exp_indi_node, calc_alg_context)
                    {
                        indi_proc_node =
                            self.incremental_node_expansion(inc_exp_indi_node, calc_alg_context);
                    }
                }
            }
        }

        // --- Probe 15: incremental compatible-merge.
        // W3-DEFER[api]: deferred merge helper. ---

        // --- Probe 16: early individual-reactivation queue (cpp 2402-2419). LIVE. ---
        if indi_proc_node.is_none() {
            let q = calc_alg_context.early_individual_reactivation_processing_queue(false);
            if q.is_some()
                && !calc_alg_context
                    .process_context()
                    .indi_reactivation_proc_queue(q)
                    .is_empty()
            {
                let q = calc_alg_context.early_individual_reactivation_processing_queue(true);
                indi_proc_node =
                    self.take_next_reactivation_individual_from_queue(q, calc_alg_context);
                self.indi_node_from_queue_type = IndiNodeQueueType::Inqt_CompCachedReact;
            }
        }

        // --- Probe 17: nominal-non-deterministic processing sort prep
        // (cpp 2421-2439). LIVE. ---
        if indi_proc_node.is_none()
            && !calc_alg_context
                .processing_data_box()
                .has_nominal_non_deterministic_processing_nodes_sorted()
        {
            let mut nom_non_det_pro_linkers = calc_alg_context
                .processing_data_box_mut()
                .take_sorted_nominal_non_deterministic_processing_node_linker();
            nom_non_det_pro_linkers.sort_by(|left, right| {
                let left_id = calc_alg_context
                    .process_context()
                    .node(*left)
                    .individual_node_id();
                let right_id = calc_alg_context
                    .process_context()
                    .node(*right)
                    .individual_node_id();
                right_id.cmp(&left_id)
            });
            calc_alg_context
                .processing_data_box_mut()
                .clear_sorted_nominal_non_deterministic_processing_node_linker();
            for nom_non_det_pro_linker in nom_non_det_pro_linkers {
                calc_alg_context
                    .processing_data_box_mut()
                    .add_sorted_nominal_non_deterministic_processing_node_linker(vec![
                        nom_non_det_pro_linker,
                    ]);
            }
            calc_alg_context
                .processing_data_box_mut()
                .set_nominal_non_deterministic_processing_nodes_sorted(true);
        }

        // --- Probe 18: prepare backend reuse-expansion branching.
        // W3-DEFER[api]: task branching + reuse-mode dependency siblings. ---

        // --- Probe 19: fixed-mode backend reuse-expansion (cpp 2453-2460). LIVE. ---
        if indi_proc_node.is_none() && self.opt_backend_expansion_reuse {
            let exp_cont_data = calc_alg_context.backend_neighbour_expansion_controlling_data(true);
            if calc_alg_context
                .process_context()
                .backend_neighbour_expansion_controlling_data(exp_cont_data)
                .is_fixed_reuse_expansion_mode()
            {
                indi_proc_node =
                    self.take_next_backend_reuse_expansion_individual(calc_alg_context);
            }
        }

        // --- Probe 20: individual-processing queue (cpp 2459-2467). LIVE. ---
        if indi_proc_node.is_none() {
            self.min_concept_processing_priority_level = 0.0;
            let q = calc_alg_context.individual_processing_queue(false);
            if q.is_some()
                && !calc_alg_context
                    .process_context()
                    .indi_proc_queue(q)
                    .is_empty()
            {
                let q = calc_alg_context.individual_processing_queue(true);
                let indi_process_node_des = calc_alg_context
                    .process_context_mut()
                    .indi_processing_queue_take_next_descriptor(q);
                indi_proc_node = calc_alg_context
                    .process_context()
                    .indi_proc_node_desc(indi_process_node_des)
                    .get_individual();
                self.indi_node_from_queue_type = IndiNodeQueueType::Inqt_Outdated;
            }
        }

        // --- Probe 21: nominal processing queue (cpp 2381-2387). LIVE. ---
        if indi_proc_node.is_none() {
            let q = calc_alg_context.get_nominal_processing_queue(false);
            if q.is_some()
                && !calc_alg_context
                    .process_context()
                    .indi_depth_proc_queue(q)
                    .is_empty()
            {
                let q = calc_alg_context.get_nominal_processing_queue(true);
                indi_proc_node = calc_alg_context
                    .process_context_mut()
                    .indi_depth_queue_take_next(q);
                self.indi_node_from_queue_type = IndiNodeQueueType::Inqt_Nominal;
            }
        }

        // --- Probes 22-23: backend individual-neighbour + propagation-cut expansion.
        // W3-DEFER[api]: backend-cache + neighbour-expansion controlling data. ---

        // --- Probe 24: sorted nominal-non-deterministic processing node
        // (cpp 2576-2581). LIVE (db4-backed `mSortedNominalNonDeterministicProcessing
        // NodeLinker`); reached only after the deferred sort-prep arm, so it is inert
        // until nominal non-deterministic nodes exist (none on the trivial path). ---
        if indi_proc_node.is_none()
            && calc_alg_context
                .processing_data_box()
                .has_sorted_nominal_non_deterministic_processing_nodes()
        {
            indi_proc_node = calc_alg_context
                .processing_data_box_mut()
                .take_sorted_nominal_non_deterministic_processing_node();
            self.indi_node_from_queue_type = IndiNodeQueueType::Inqt_Nominal;
        }

        // --- Probe 25: individual depth processing queue (cpp 2589-2595). LIVE. ---
        if indi_proc_node.is_none() {
            let q = calc_alg_context.get_individual_depth_processing_queue(false);
            if q.is_some()
                && !calc_alg_context
                    .process_context()
                    .indi_depth_proc_queue(q)
                    .is_empty()
            {
                let q = calc_alg_context.get_individual_depth_processing_queue(true);
                indi_proc_node = calc_alg_context
                    .process_context_mut()
                    .indi_depth_queue_take_next(q);
                self.indi_node_from_queue_type = IndiNodeQueueType::Inqt_DepthNormal;
            }
        }

        // --- Probe 26: nominal-caching-loss reactivation. W3-DEFER[api]:
        // `getUpToDateIndividual` MISS path + PRFSATURATIONBLOCKINGCACHED flags. ---

        // --- Probe 27: individual depth-first queue (cpp 2613-2619). LIVE. ---
        if indi_proc_node.is_none() {
            let q = calc_alg_context.get_individual_depth_first_processing_queue(false);
            if q.is_some()
                && !calc_alg_context
                    .process_context()
                    .indi_unsorted_proc_queue(q)
                    .is_empty()
            {
                let q = calc_alg_context.get_individual_depth_first_processing_queue(true);
                indi_proc_node = calc_alg_context
                    .process_context_mut()
                    .indi_unsorted_proc_queue_mut(q)
                    .take_next_process_individual_node();
                self.indi_node_from_queue_type = IndiNodeQueueType::Inqt_DepthFirst;
            }
        }

        // --- Probe 28: late individual-reactivation queue (cpp 2621-2640). LIVE. ---
        if indi_proc_node.is_none() {
            let q = calc_alg_context.late_individual_reactivation_processing_queue(false);
            if q.is_some()
                && !calc_alg_context
                    .process_context()
                    .indi_reactivation_proc_queue(q)
                    .is_empty()
            {
                let q = calc_alg_context.late_individual_reactivation_processing_queue(true);
                indi_proc_node =
                    self.take_next_reactivation_individual_from_queue(q, calc_alg_context);
                self.indi_node_from_queue_type = IndiNodeQueueType::Inqt_CompCachedReact;
            }
        }

        // --- Probe 29: blocking-update review queue (cpp 2643-2650). LIVE. ---
        if indi_proc_node.is_none() {
            // mOptDetExpPreporcessing = false;
            self.opt_det_exp_preporcessing = false;
            let q = calc_alg_context.get_blocking_update_review_processing_queue(false);
            if q.is_some()
                && !calc_alg_context
                    .process_context()
                    .indi_depth_proc_queue(q)
                    .is_empty()
            {
                let q = calc_alg_context.get_blocking_update_review_processing_queue(true);
                indi_proc_node = calc_alg_context
                    .process_context_mut()
                    .indi_depth_queue_take_next(q);
                self.indi_node_from_queue_type = IndiNodeQueueType::Inqt_BlockUp;
            }
        }

        // --- Probe 30: blocked-reactivation queue (cpp 2652-2658). LIVE. ---
        if indi_proc_node.is_none() {
            let q = calc_alg_context.get_blocked_reactivation_processing_queue(false);
            if q.is_some()
                && !calc_alg_context
                    .process_context()
                    .indi_depth_proc_queue(q)
                    .is_empty()
            {
                let q = calc_alg_context.get_blocked_reactivation_processing_queue(true);
                indi_proc_node = calc_alg_context
                    .process_context_mut()
                    .indi_depth_queue_take_next(q);
                self.indi_node_from_queue_type = IndiNodeQueueType::Inqt_BlockReact;
            }
        }

        // --- Probe 31: signature-blocking review set (cpp 2661-2694). LIVE. ---
        if indi_proc_node.is_none() {
            let q = calc_alg_context.signature_blocking_review_set(false);
            if q.is_some()
                && !calc_alg_context
                    .process_context()
                    .signature_blocking_review_set(q)
                    .is_empty()
            {
                let q = calc_alg_context.signature_blocking_review_set(true);
                let next_review = calc_alg_context
                    .process_context_mut()
                    .signature_blocking_review_set_mut(q)
                    .take_next_review_individual();
                if let Some((blocked_indi_id, is_non_subset_data)) = next_review {
                    indi_proc_node =
                        self.get_localized_individual_by_id(blocked_indi_id, calc_alg_context);

                    if !is_non_subset_data && self.conf_individual_reusing_from_signature_blocking {
                        self.upgrade_signature_blocking_to_individual_reusing(
                            indi_proc_node,
                            calc_alg_context,
                        );
                    }

                    let loc_sig_blocking_data = self
                        .get_or_create_signature_blocking_concept_expansion_data(
                            indi_proc_node,
                            calc_alg_context,
                        );
                    if !calc_alg_context
                        .process_context()
                        .sig_block_con_exp_data(loc_sig_blocking_data)
                        .is_identic_concept_set_required()
                    {
                        calc_alg_context
                            .process_context_mut()
                            .sig_block_con_exp_data_mut(loc_sig_blocking_data)
                            .set_identic_concept_set_required(true);
                        calc_alg_context
                            .process_context_mut()
                            .node_mut(indi_proc_node)
                            .set_last_search_blocker_candidate_count(0);
                        self.detect_individual_node_signature_blocking_status(
                            indi_proc_node,
                            calc_alg_context,
                        );
                    }
                }
            }
        }

        // --- Probe 32: reusing review data (cpp 2698-2714). LIVE. ---
        if indi_proc_node.is_none() {
            let q = calc_alg_context.reusing_review_data(false);
            if q.is_some()
                && !calc_alg_context
                    .process_context()
                    .reusing_review_data(q)
                    .is_empty()
            {
                let q = calc_alg_context.reusing_review_data(false);
                while calc_alg_context
                    .process_context()
                    .reusing_review_data(q)
                    .has_next_individual_id()
                    && indi_proc_node.is_none()
                {
                    let indi_node_id = calc_alg_context
                        .process_context_mut()
                        .reusing_review_data_mut(q)
                        .take_next_individual_id();

                    indi_proc_node =
                        self.get_localized_individual_by_id(indi_node_id, calc_alg_context);
                    let reuse_data = calc_alg_context
                        .process_context()
                        .node(indi_proc_node)
                        .reusing_individual_node_concept_expansion_data(false);
                    if !calc_alg_context
                        .process_context()
                        .reusing_con_exp_data(reuse_data)
                        .is_concept_set_still_subset()
                    {
                        self.remove_individual_reusing(&mut indi_proc_node, calc_alg_context);
                    } else {
                        indi_proc_node = NodeId::NONE;
                    }
                }
            }
        }

        // --- Probe 33: backend late-neighbour expansion.
        // W3-DEFER[api]: backend-neighbour expansion cursor. ---

        // --- Probe 34: prioritized-mode backend reuse-expansion (cpp 2734-2741). LIVE. ---
        if indi_proc_node.is_none() && self.opt_backend_expansion_reuse {
            let exp_cont_data = calc_alg_context.backend_neighbour_expansion_controlling_data(true);
            if calc_alg_context
                .process_context()
                .backend_neighbour_expansion_controlling_data(exp_cont_data)
                .is_prioritized_reuse_expansion_mode()
            {
                indi_proc_node =
                    self.take_next_backend_reuse_expansion_individual(calc_alg_context);
            }
        }

        // --- Probe 35: delaying-nominal processing queue (cpp 2761-2767). LIVE. ---
        if indi_proc_node.is_none() {
            let q = calc_alg_context.get_delaying_nominal_processing_queue(false);
            if q.is_some() {
                let q = calc_alg_context.get_delaying_nominal_processing_queue(true);
                indi_proc_node = calc_alg_context
                    .process_context_mut()
                    .indi_unsorted_proc_queue_mut(q)
                    .take_next_process_individual_node();
                self.indi_node_from_queue_type = IndiNodeQueueType::Inqt_DelayedNominal;
            }
        }

        // --- Probe 36: backend indirect-compatibility expansion. W3-DEFER[api]:
        // `getCorrectedNominalIndividualNode` + backend-cache sync/expansion. ---

        // return indiProcNode;
        indi_proc_node
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::analyzeCompletionGraphStatistics`.
    pub fn analyze_completion_graph_statistics(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // CProcessingDataBox* processingDataBox = calcAlgContext->getProcessingDataBox();
        // CIndividualProcessNodeVector* indiNodeVec = processingDataBox->getIndividualProcessNodeVector();
        // cint64 indiCount = indiNodeVec->getItemCount();
        let indi_count: Cint64 = calc_alg_context
            .processing_data_box()
            .individual_process_node_vector()
            .get_item_count();
        // cint64 indiStart = indiNodeVec->getItemMinIndex();
        let indi_start: Cint64 = calc_alg_context
            .processing_data_box()
            .individual_process_node_vector()
            .get_item_min_index();

        let mut indi_idx = indi_start;
        while indi_idx < indi_count {
            // CIndividualProcessNode* indiNode = getLocalizedIndividual(indiIdx,calcAlgContext);
            let mut indi_node: NodeId = calc_alg_context.get_localized_individual_by_id(indi_idx);
            if indi_node.is_some() {
                // CReapplyConceptLabelSet* conSet = indiNode->getReapplyConceptLabelSet(false);
                let con_set: LabelSetId = calc_alg_context
                    .process_context_mut()
                    .node_mut(indi_node)
                    .get_reapply_concept_label_set(false);
                // cint64 conSigValue = indiNode->getReapplyConceptLabelSet(false)->getConceptSignatureValue();
                let con_sig_value: Cint64 = if con_set.is_some() {
                    calc_alg_context
                        .process_context()
                        .label_set(con_set)
                        .get_concept_signature_value()
                } else {
                    0
                };
                // cint64 processingRestrictionFlags = indiNode->getProcessingRestrictionFlags();
                let processing_restriction_flags: Cint64 = calc_alg_context
                    .process_context()
                    .node(indi_node)
                    .processing_restriction_flags();
                // KONCLUDE-PORT-NOTE[api]: QHash::insertMulti (a multimap insert) →
                // HashMap::insert; `signature_indi_node_status_hash` is single-valued
                // (statistics-only field), so duplicate-key keeps only the last value.
                self.signature_indi_node_status_hash
                    .insert(con_sig_value, processing_restriction_flags);

                if !self
                    .signature_indi_node_pred_dep_hash
                    .contains_key(&con_sig_value)
                {
                    // cint64 indiAncestorDepth = indiNode->getIndividualAncestorDepth();
                    let indi_ancestor_depth: Cint64 = calc_alg_context
                        .process_context()
                        .node(indi_node)
                        .individual_ancestor_depth();
                    if con_set.is_some() && indi_ancestor_depth > 0 {
                        let mut con_from_pred_count: Cint64 = 0;
                        // CConceptDescriptor* conDesIt = conSet->getAddingSortedConceptDescriptionLinker();
                        let mut con_des_it: ConDescId = calc_alg_context
                            .process_context()
                            .label_set(con_set)
                            .get_adding_sorted_concept_description_linker();
                        while con_des_it.is_some() {
                            // cint64 conceptTag = conDesIt->getConceptTag();
                            let concept_tag: Cint64 = {
                                let onto = calc_alg_context.ontology_arenas();
                                calc_alg_context
                                    .process_context()
                                    .con_desc(con_des_it)
                                    .get_concept_tag(onto)
                            };
                            if concept_tag != 1 {
                                // CDependencyTrackPoint* depTrackPoint = conDesIt->getDependencyTrackPoint();
                                let dep_track_point: TrackPointId = calc_alg_context
                                    .process_context()
                                    .con_desc(con_des_it)
                                    .get_dependency_track_point();
                                // if (isConceptFromPredecessorDependent(indiNode,conDesIt,depTrackPoint,calcAlgContext))
                                if self.is_concept_from_predecessor_dependent(
                                    &mut indi_node,
                                    con_des_it,
                                    dep_track_point,
                                    calc_alg_context,
                                ) {
                                    con_from_pred_count += 1;
                                }
                            }
                            // conDesIt = conDesIt->getNext();
                            con_des_it = calc_alg_context
                                .process_context()
                                .con_desc(con_des_it)
                                .get_next_concept_descriptor();
                        }
                        self.signature_indi_node_pred_dep_hash
                            .insert(con_sig_value, con_from_pred_count);
                    }
                }
            }
            indi_idx += 1;
        }

        // mIndiNodeCountMap.insert(indiCount,mIndiNodeCountMap.value(indiCount,0)+1);
        let prev_count = *self.indi_node_count_map.get(&indi_count).unwrap_or(&0);
        self.indi_node_count_map.insert(indi_count, prev_count + 1);
        // mIndiNodeCountList.append(indiCount);
        self.indi_node_count_list.push(indi_count);
    }
}
