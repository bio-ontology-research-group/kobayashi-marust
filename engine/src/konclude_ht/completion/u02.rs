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

use super::super::model::substrate::{Cint64, Id, NegLink};
use super::super::model::ConceptId;
use super::super::process::node::IndividualProcessNode;
use super::super::process::queues::{ConceptProcessingQueue, ConceptProcessingQueueId};
use super::super::process::{ConDescId, LabelSetId, NodeId, TrackPointId};
use super::algorithm::{BranchKind, IndiNodeQueueType, DETERMINISTIC_PROCESS_PRIORITY};
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
        let progress = std::env::var_os("KM_BRIDGE_PROGRESS").is_some();
        // KM_BRIDGE_MAX_DRIVES: per-call drive cap — on overrun raise a STOP
        // (an UNKNOWN verdict; callers defer). A single pathological search
        // must never wedge a classify run.
        let max_drives: u64 = std::env::var("KM_BRIDGE_MAX_DRIVES")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(u64::MAX);
        let mut drives: u64 = 0;
        self.ddb_root_cancelled = false;
        loop {
            if drives >= max_drives {
                calc_alg_context.raise_stop(false);
                return false;
            }
            // Per-probe wall-clock deadline (see `drive_deadline`): a STOP is
            // an UNKNOWN verdict — the caller DEFERS; never fold into (un)sat.
            if let Some(deadline) = self.drive_deadline {
                if std::time::Instant::now() >= deadline {
                    calc_alg_context.raise_stop(false);
                    return false;
                }
            }
            self.run_saturation_loop(calc_alg_context);
            drives += 1;
            if progress && drives % 4096 == 0 {
                eprintln!(
                    "PROGRESS drives={drives} backtracks={} nodes={} inserts={} bp_depth={} ddb_jumps={} ddb_pops={} ddb_fallbacks={} ddb_marks={} ddb_line_fails={}",
                    self.or_backtrack_count,
                    calc_alg_context.process_context().node_count(),
                    self.stat_con_des_insertion_count,
                    self.or_branch_stack.len(),
                    self.ddb_jump_count,
                    self.ddb_jump_pop_total,
                    self.ddb_fallback_count,
                    self.ddb_mark_count,
                    self.ddb_line_init_fail_count,
                );
                eprintln!(
                    "PROGRESS-DDB already_marked={} refuted_discards={}",
                    self.ddb_already_marked_count, self.ddb_refuted_discard_count
                );
            }
            if !calc_alg_context.has_pending_signal() {
                // fixpoint reached, no clash ⇒ consistent / complete.
                return true;
            }
            match calc_alg_context.pending_signal() {
                CalcSignal::Clash(clash) => {
                    if self.conf_dependency_backjumping {
                        // Dependency-directed backjumping: run the ported
                        // `clashedBacktracking` (u29) — it walks the clash's
                        // dependency closure and marks the responsible
                        // non-deterministic track points clashed (propagating
                        // through decisions whose every sibling is clashed).
                        self.clashed_backtracking(clash, calc_alg_context);
                        if self.ddb_root_cancelled {
                            // The clash traced to branching level 0: independent
                            // of every open alternative ⇒ INCONSISTENT.
                            self.ht_dump_final_clash(clash, "ddb-root-cancel", calc_alg_context);
                            return false;
                        }
                        if self.try_backtrack_or_branch_ddb(calc_alg_context) {
                            continue;
                        }
                        self.ht_dump_final_clash(clash, "ddb-exhausted", calc_alg_context);
                        return false;
                    }
                    if self.try_backtrack_or_branch(calc_alg_context) {
                        // advanced to the next alternative (signal cleared); re-drive.
                        continue;
                    }
                    // no open branch point with a remaining alternative ⇒ the clash is
                    // unrecoverable: the completion graph is INCONSISTENT.
                    self.ht_dump_final_clash(clash, "chrono-exhausted", calc_alg_context);
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
    /// Discard the topmost branch point: pop its stack entry, close its
    /// branch epoch (in-process COW — the complete-state rollback), restore
    /// the used branch tree node.
    fn discard_topmost_or_branch(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let bp = self.or_branch_stack.pop().expect("caller checked non-empty");
        if bp.own_epoch {
            calc_alg_context.pop_branch_epoch();
        } else {
            // No COW: nodes created since the push belong to REFUTED
            // alternatives and linger in the arena as phantoms — record the
            // interval so the singleton scan skips them.
            let now = calc_alg_context.process_context().node_count();
            if now > bp.node_count_at_push && !self.singleton_concepts.is_empty() {
                self.phantom_node_intervals
                    .push((bp.node_count_at_push, now));
            }
        }
        calc_alg_context.base.used_branch_tree_node = bp.parent_used_branch_node;
        self.or_backtrack_count += 1;
    }

    fn try_backtrack_or_branch(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // discard branch points whose every alternative has already clashed.
        while let Some(bp) = self.or_branch_stack.last() {
            if bp.next_alt < bp.alternatives_len() {
                break;
            }
            self.discard_topmost_or_branch(calc_alg_context);
        }
        if self.or_branch_stack.is_empty() {
            return false;
        }
        self.advance_topmost_or_branch(calc_alg_context);
        true
    }

    /// The dependency-directed backtrack (`conf_dependency_backjumping`): the
    /// caller has already run `clashedBacktracking` (u29), which marked every
    /// non-deterministic track point the clash depends on as clashed
    /// (`is_clashed_or_irelevant_branch`), propagating through decisions whose
    /// every sibling alternative is clashed. The stack walk then:
    ///
    /// - POPS a branch point whose current alternative's track point is NOT
    ///   marked — the clash does not depend on that choice, so the clash
    ///   recurs under every one of its alternatives; enumerating them is
    ///   futile (the backjump — this is what collapses 541's 2^56 space).
    ///   Sound because the tracked-clash line analyses the DEEPEST branching
    ///   level first (`getBranchingLevelTag() == mBranchingLevel` bucketing):
    ///   an unmarked branch point above the analysis stop is not in the
    ///   clash's dependency closure.
    /// - POPS a marked-but-exhausted branch point (the u29 propagation has
    ///   already marked the outer responsible decision when the last sibling
    ///   clashed).
    /// - ADVANCES the topmost marked branch point with a remaining
    ///   alternative.
    ///
    /// SAFETY NET: when the analysis marked NO branch point that still has a
    /// remaining alternative (e.g. it stopped early on a track point already
    /// marked by an earlier clash epoch — possible because the in-process
    /// label-snapshot restore cannot undo multi-node leakage the way
    /// Konclude's per-task copy-on-write does), the walk does NOT declare
    /// inconsistency: it falls back to the chronological backtrack. DDB is
    /// therefore purely a pruner — a wrong UNSAT verdict cannot come from the
    /// marking, only from exhausting alternatives (modulo the pop-unmarked
    /// skip, which is justified per-clash by the level-ordering argument).
    fn try_backtrack_or_branch_ddb(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // Leftover guard: once ANY advance skipped its snapshot restore the
        // labels may carry branch-dependent leftovers whose descriptors
        // reference STALE track points — a clash involving them does not
        // satisfy the level-ordering argument, so the pop-unmarked skip could
        // discard live alternatives (measured: ore_ont_12653 under DDB grew 4
        // spurious subsumptions). Chronological fallback owns the search then;
        // the root-level cancellation stays in force (leftovers cannot appear
        // in a branching-level-0 closure — their tags are > 0).
        if self.unrestored_advance_count > 0 {
            return self.try_backtrack_or_branch(calc_alg_context);
        }
        // Scan (no mutation) from the top for the first branch point whose
        // CURRENT alternative the analysis marked clashed. Two cases:
        // - it still has an unexplored alternative → backjump and ADVANCE it;
        // - it is EXHAUSTED → the whole decision is refuted, and every branch
        //   point ABOVE it lives inside the refuted alternative's context —
        //   DISCARD through it and re-run the backtrack on the remaining
        //   stack. Without this second case the chronological fallback keeps
        //   searching INSIDE the refuted subtree: the same clash re-traces to
        //   the same marked track point, the analysis early-outs
        //   (already-marked), and the search thrashes (measured on
        //   ore_ont_12653 PathOfLength3: already_marked == fallbacks ==
        //   ~100% of 2.9M backtracks against one exhausted mid-stack mark —
        //   Konclude gets the escape for free from branch-task cancellation).
        let mut target: Option<(usize, bool)> = None;
        for i in (0..self.or_branch_stack.len()).rev() {
            let bp = &self.or_branch_stack[i];
            let cur_tp = bp
                .alt_track_points
                .get(bp.next_alt.wrapping_sub(1))
                .copied()
                .unwrap_or(TrackPointId::NONE);
            let refuted = cur_tp.is_some()
                && calc_alg_context
                    .process_context()
                    .track_point(cur_tp)
                    .is_clashed_or_irelevant_branch();
            if refuted {
                target = Some((i, bp.next_alt < bp.alternatives_len()));
                break;
            }
        }
        let Some((target, has_remaining)) = target else {
            // No marked branch point — do NOT trust the analysis for an UNSAT
            // verdict; chronological fallback.
            self.ddb_fallback_count += 1;
            return self.try_backtrack_or_branch(calc_alg_context);
        };
        if !has_remaining {
            // refuted AND exhausted: discard the refuted decision (and the
            // subtree stacked above it), then retry the backtrack below.
            //
            // KM_HT_DDB_REFUTED_DISCARD (opt-in): this escape collapses the
            // stale-mark thrash (ore_ont_12653 PathOfLength3 read-off: 120 s /
            // 2.9 M backtracks → 10.5 s), BUT it drives the search into the
            // still-buggy u29 all-siblings-refuted propagation, whose
            // collected closure degenerates to the decision's own tag-0 cause
            // and wrongly ROOT-CANCELS (measured: 12 spurious
            // PathOfLength3 ⊑ X; same single-descriptor closure signature as
            // the pre-2a869e8 bug — the before-proc-tag remainder loses the
            // non-local causes). Default OFF until that stepping is fixed
            // against cpp 7677–7776; the fast repro NEEDS this flag.
            if std::env::var_os("KM_HT_DDB_REFUTED_DISCARD").is_some() {
                self.ddb_refuted_discard_count += 1;
                while self.or_branch_stack.len() > target {
                    self.discard_topmost_or_branch(calc_alg_context);
                }
                if self.or_branch_stack.is_empty() {
                    return false;
                }
                return self.try_backtrack_or_branch_ddb(calc_alg_context);
            }
            // default: chronological fallback (sound; thrashy on stale marks).
            self.ddb_fallback_count += 1;
            return self.try_backtrack_or_branch(calc_alg_context);
        };
        self.ddb_jump_count += 1;
        self.ddb_jump_pop_total += (self.or_branch_stack.len() - 1 - target) as u64;
        // The backjump: discard everything above the target. Unmarked branch
        // points there are not in the clash's dependency closure (the tracked
        // line analyses the deepest branching level first), so the clash
        // recurs under every one of their alternatives; marked-but-exhausted
        // ones were propagated through by u29 when their last sibling clashed.
        while self.or_branch_stack.len() > target + 1 {
            self.discard_topmost_or_branch(calc_alg_context);
        }
        self.advance_topmost_or_branch(calc_alg_context);
        true
    }

    /// Shared advance: clear the pending clash, restore the topmost branch
    /// point's snapshots, re-seed its node, and add its next unexplored
    /// alternative (under the alternative's own non-deterministic track point
    /// when DDB minted them, else under the disjunction's track point).
    fn advance_topmost_or_branch(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        self.or_backtrack_count += 1;

        // In-process COW: close the FAILED alternative's epoch (complete
        // graph rollback to the pre-alternative state) and open a fresh one
        // for the next alternative — the in-process equivalent of killing the
        // clashed branch task and starting its sibling from the parent's
        // copy-on-write databox. Keyed on the branch point's OWN epoch flag:
        // at-most merge branch points carry an epoch even when the global COW
        // mode is off (a merge is not undoable by the label snapshot).
        let topmost_own_epoch = self
            .or_branch_stack
            .last()
            .map(|bp| bp.own_epoch)
            .unwrap_or(false);
        if topmost_own_epoch {
            calc_alg_context.pop_branch_epoch();
            calc_alg_context.push_branch_epoch();
        } else if !self.singleton_concepts.is_empty() {
            // No COW: the FAILED alternative's created nodes linger as
            // phantoms (see `phantom_node_intervals`) — record them before
            // the next alternative starts appending.
            let at_push = self
                .or_branch_stack
                .last()
                .map(|bp| bp.node_count_at_push)
                .unwrap_or(usize::MAX);
            let now = calc_alg_context.process_context().node_count();
            if now > at_push {
                self.phantom_node_intervals.push((at_push, now));
            }
        }

        // the clash is being recovered from — clear it (the C++ catch consumes the
        // exception, then `clashedBacktracking` re-drives the chosen branch).
        calc_alg_context.clear_pending_signal();

        // At-most merge branch point: the next alternative MERGES a different
        // successor pair (`mergeMergingIndividualNodesPairwise` sibling task).
        // The epoch pop above restored the exact push-time state, so the pair's
        // node ids are valid again.
        if matches!(
            self.or_branch_stack.last().map(|bp| &bp.kind),
            Some(BranchKind::AtMostMerge(_))
        ) {
            self.advance_atmost_merge_alternative(calc_alg_context);
            return;
        }
        // Choose branch point: the second alternative qualifies the successor
        // POSITIVELY (the `qualNeg = false` sibling task).
        if matches!(
            self.or_branch_stack.last().map(|bp| &bp.kind),
            Some(BranchKind::AtMostQualify { .. })
        ) {
            self.advance_atmost_qualify_alternative(calc_alg_context);
            return;
        }

        // advance the topmost open branch to its next unexplored alternative.
        let (node, target, op_negated, dep_track_point, node_count_at_push, sem_branch) = {
            let bp = self.or_branch_stack.last_mut().expect("checked non-empty");
            let link = bp.disjuncts[bp.next_alt];
            let alt_tp = bp.alt_track_points.get(bp.next_alt).copied();
            // Semantic branching (`executeORBranching` non-pos operands): the
            // new alternative also asserts the NEGATION of every previously
            // refuted alternative (`addOpNegated = !posOperand ^ isNegated ^
            // negate`), so a sibling subtree cannot re-explore a failed
            // disjunct. Sound: alternative `i` is only advanced past when the
            // context refuted it. Konclude default: atomic-only
            // (`AtomicSemanticBranching`, no extra rule work).
            let sem_branch: Vec<NegLink<ConceptId>> = if self.conf_semantic_branching
                || self.conf_atomic_semantic_branching
            {
                bp.disjuncts[..bp.next_alt]
                    .iter()
                    .map(|l| NegLink {
                        target: l.target,
                        negated: !(l.negated ^ bp.negate),
                    })
                    .collect()
            } else {
                Vec::new()
            };
            bp.next_alt += 1;
            (
                bp.node,
                link.target,
                link.negated ^ bp.negate,
                alt_tp.filter(|tp| tp.is_some()).unwrap_or(bp.dep_track_point),
                bp.node_count_at_push,
                sem_branch,
            )
        };
        // DDB: the new alternative's branch node becomes the used branch tree
        // node (nested disjunctions under it nest one branching level deeper).
        if dep_track_point.is_some()
            && self
                .or_branch_stack
                .last()
                .map(|bp| !bp.alt_track_points.is_empty())
                .unwrap_or(false)
        {
            calc_alg_context.base.used_branch_tree_node = calc_alg_context
                .process_context()
                .track_point(dep_track_point)
                .get_branch_node();
        }

        // SOUND-BACKTRACK: restore `node`'s label set to the pre-disjunction
        // snapshot, undoing the just-failed alternative's derivations, so the next
        // alternative is tried on the clean state. Guarded on `node_count`: if the
        // failed alternative created a successor node, the single-node snapshot
        // cannot restore the graph (that needs the full task-fork restore), so we
        // leave the chronological behaviour unchanged for that case (no regression).
        // Under in-process COW the epoch rollback already restored the
        // complete state — the single-node snapshot is redundant (and empty).
        let restored = topmost_own_epoch
            || calc_alg_context.process_context().node_count() == node_count_at_push;
        if !restored {
            self.unrestored_advance_count += 1;
        }
        if !topmost_own_epoch && restored {
            let (label_snapshot, queue_snapshot) = {
                let bp = self.or_branch_stack.last().expect("checked non-empty");
                (bp.node_label_snapshot.clone(), bp.node_queue_snapshot.clone())
            };
            let ls_id = calc_alg_context
                .process_context_mut()
                .node_reapply_concept_label_set(node);
            *calc_alg_context
                .process_context_mut()
                .label_set_mut(ls_id) = label_snapshot;
            // Restore the coupled processing-queue snapshot (see `OrBranchPoint`):
            // trigger descriptors consumed by the failed alternative re-appear, so
            // reapply registrations wiped by the label restore are re-derived.
            let q_id = calc_alg_context
                .process_context_mut()
                .node_concept_processing_queue(node, true);
            *calc_alg_context
                .process_context_mut()
                .concept_proc_queue_mut(q_id) = queue_snapshot;
        }

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
        // Semantic-branching additions (under the SAME alternative track
        // point, exactly `executeORBranching`'s addingConceptLinker). Stop on
        // a raised clash — the outer loop backtracks again.
        //
        // ONLY when the snapshot restore actually executed: Konclude adds
        // these in a FORKED task (pre-branch state by construction). When the
        // failed alternative created successor nodes the single-node snapshot
        // cannot restore the graph and the label keeps the failed
        // alternative's derivations — adding ¬d_i on top of leftover d_i
        // derivations manufactures false clashes (measured: 12653 collapsed
        // to unsat-everything, spurious=120). Without the restore, skip the
        // negations entirely (the plain chronological add is the validated
        // behaviour there).
        if restored {
            for l in sem_branch {
                if calc_alg_context.has_pending_signal() {
                    break;
                }
                if self.conf_semantic_branching
                    || self.is_concept_addition_atomaric(l.target, l.negated, calc_alg_context)
                {
                    let mut n = node_m;
                    self.add_concept_to_individual(
                        l.target,
                        l.negated,
                        &mut n,
                        dep_track_point,
                        true,
                        true,
                        calc_alg_context,
                    );
                }
            }
        }
    }

    /// Advance the topmost (at-most merge) branch point to its next merge-pair
    /// alternative: perform the pair's merge under the alternative's track
    /// point, relocate the counted parent's links, re-seed the parent, and
    /// re-check the at-most bound (which may push a nested merge branch point
    /// or raise the genuine at-most clash). The caller has already rolled the
    /// epoch back to the push-time state and cleared the pending signal.
    ///
    /// This is the in-process realisation of one sibling
    /// `createMergeBranchingTask` of `mergeMergingIndividualNodesPairwise`
    /// (cpp 15044–15093); the bound RE-CHECK stands in for Konclude's
    /// reapplication-driven re-fire of the at-most concept (cpp 15001–15005).
    fn advance_atmost_merge_alternative(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let (parent, into, from, alt_tp, dep_track_point, role, concept_linker, negate, cardinality, con_des) = {
            let bp = self.or_branch_stack.last_mut().expect("caller checked topmost");
            let BranchKind::AtMostMerge(m) = &bp.kind else {
                unreachable!("caller checked kind")
            };
            let (into, from) = m.pairs[bp.next_alt];
            let alt_tp = bp
                .alt_track_points
                .get(bp.next_alt)
                .copied()
                .filter(|tp| tp.is_some());
            bp.next_alt += 1;
            (
                m.parent,
                into,
                from,
                alt_tp,
                bp.dep_track_point,
                m.role,
                m.concept_linker.clone(),
                m.negate,
                m.cardinality,
                m.con_des,
            )
        };
        // DDB: the alternative's branch node becomes the used branch tree node
        // (decisions nested under this merge nest one branching level deeper).
        let add_tp = if let Some(tp) = alt_tp {
            calc_alg_context.base.used_branch_tree_node = calc_alg_context
                .process_context()
                .track_point(tp)
                .get_branch_node();
            tp
        } else {
            dep_track_point
        };
        if std::env::var_os("KM_BRIDGE_WATCH_MERGE").is_some() {
            eprintln!(
                "ATMOST-MERGE-ALT parent=n{} merge n{} -> n{}",
                parent.index(),
                from.index(),
                into.index()
            );
        }
        self.merge_individual_node_into(into, from, add_tp, calc_alg_context);
        if !calc_alg_context.has_pending_signal() {
            self.ht_relocate_incoming_links(parent, from, into, add_tp, calc_alg_context);
        }
        // re-seed the counted parent so the drive picks it up again.
        let iq = calc_alg_context.get_individual_immediately_processing_queue(true);
        calc_alg_context
            .process_context_mut()
            .indi_unsorted_proc_queue_mut(iq)
            .insert_indiviudal_process_node(parent);
        // bound re-check on the merged graph (the reapplication re-fire).
        if !calc_alg_context.has_pending_signal() {
            let mut parent_m = parent;
            self.ht_apply_atmost_merge(
                &mut parent_m,
                role,
                &concept_linker,
                negate,
                cardinality,
                dep_track_point,
                con_des,
                calc_alg_context,
            );
        }
    }

    /// Advance the topmost (choose) branch point to its second alternative:
    /// qualify the successor POSITIVELY (each operand added with its own
    /// polarity — Konclude's `addConceptsToIndividual(conceptOpLinkerIt, false,
    /// …)` in the `qualNeg = false` sibling of `qualifyMergingIndividualNodes`,
    /// cpp 15787), re-seed successor + parent, and re-fire the at-most bound
    /// check (the successor is now a merge candidate). The caller has already
    /// rolled the epoch back and cleared the pending signal.
    fn advance_atmost_qualify_alternative(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let (succ, alt_tp, dep_track_point, parent, role, concept_linker, negate, cardinality, con_des) = {
            let bp = self.or_branch_stack.last_mut().expect("caller checked topmost");
            let BranchKind::AtMostQualify { succ, atmost } = &bp.kind else {
                unreachable!("caller checked kind")
            };
            let alt_tp = bp
                .alt_track_points
                .get(bp.next_alt)
                .copied()
                .filter(|tp| tp.is_some());
            bp.next_alt += 1;
            (
                *succ,
                alt_tp,
                bp.dep_track_point,
                atmost.parent,
                atmost.role,
                atmost.concept_linker.clone(),
                atmost.negate,
                atmost.cardinality,
                atmost.con_des,
            )
        };
        let add_tp = if let Some(tp) = alt_tp {
            calc_alg_context.base.used_branch_tree_node = calc_alg_context
                .process_context()
                .track_point(tp)
                .get_branch_node();
            tp
        } else {
            dep_track_point
        };
        if std::env::var_os("KM_BRIDGE_WATCH_MERGE").is_some() {
            eprintln!(
                "ATMOST-QUALIFY-ALT parent=n{} succ=n{} qualNeg=false",
                parent.index(),
                succ.index()
            );
        }
        // qualify positively: each operand with its OWN polarity (qualNeg=false).
        for nl in &concept_linker {
            if calc_alg_context.has_pending_signal() {
                break;
            }
            let mut s = succ;
            self.add_concept_to_individual(
                nl.target,
                nl.negated,
                &mut s,
                add_tp,
                true,
                true,
                calc_alg_context,
            );
        }
        // re-seed the qualified successor and the counted parent.
        let iq = calc_alg_context.get_individual_immediately_processing_queue(true);
        calc_alg_context
            .process_context_mut()
            .indi_unsorted_proc_queue_mut(iq)
            .insert_indiviudal_process_node(succ);
        let iq2 = calc_alg_context.get_individual_immediately_processing_queue(true);
        calc_alg_context
            .process_context_mut()
            .indi_unsorted_proc_queue_mut(iq2)
            .insert_indiviudal_process_node(parent);
        // the at-most re-fire (the successor now counts).
        if !calc_alg_context.has_pending_signal() {
            let mut parent_m = parent;
            self.ht_apply_atmost_merge(
                &mut parent_m,
                role,
                &concept_linker,
                negate,
                cardinality,
                dep_track_point,
                con_des,
                calc_alg_context,
            );
        }
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
        let progress = std::env::var_os("KM_BRIDGE_PROGRESS").is_some();
        let mut drive_iters: u64 = 0;
        macro_rules! drive_progress {
            () => {
                if progress && drive_iters % 1_000_000 == 0 {
                    eprintln!(
                        "PROGRESS-SAT iters={drive_iters} nodes={} inserts={}",
                        calc_alg_context.process_context().node_count(),
                        self.stat_con_des_insertion_count,
                    );
                }
            };
        }
        let mut indi_proc_node: NodeId = self.take_next_process_individual(calc_alg_context);
        if calc_alg_context.has_pending_signal() {
            return;
        }
        while indi_proc_node.is_some() {
            drive_iters += 1;
            drive_progress!();
            // Per-probe wall-clock deadline also applies WITHIN a drive: a
            // single saturation drive can run millions of rule firings (and
            // under COW journaling, tens of GB) before returning to the outer
            // drive loop's check.
            if drive_iters % 4096 == 0 {
                if let Some(deadline) = self.drive_deadline {
                    if std::time::Instant::now() >= deadline {
                        calc_alg_context.raise_stop(false);
                        return;
                    }
                }
            }
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
                    drive_progress!();
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
            // KM-BRIDGE singleton-concept merge: at candidate fixpoint (no next
            // individual) run the deterministic value-identity merges; a merge
            // re-queues work, so re-take. True fixpoint only when the scan is
            // dry. Scan-at-fixpoint (not insert-hooked) is branch-safe by
            // construction: it is a pure function of the CURRENT branch state,
            // so backtracking needs no queue rollback.
            if indi_proc_node.is_none() && !self.singleton_concepts.is_empty() {
                let merged = self.ht_apply_singleton_merges(calc_alg_context);
                if calc_alg_context.has_pending_signal() {
                    return;
                }
                if merged {
                    indi_proc_node = self.take_next_process_individual(calc_alg_context);
                    if calc_alg_context.has_pending_signal() {
                        return;
                    }
                }
            }
        }
    }

    /// KM_BRIDGE_DUMP_CLASH: print the FINAL (verdict-deciding) clash's
    /// descriptor chain — concept tags, polarity, node ids — the ground truth
    /// for spurious-unsat hunts (which concepts on which nodes actually
    /// contradicted, and via which backtrack outcome).
    fn ht_dump_final_clash(
        &mut self,
        clash: super::super::process::ClashDescId,
        how: &str,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        if std::env::var_os("KM_BRIDGE_DUMP_CLASH").is_none() || self.ddb_analysis_dumps >= 8 {
            return;
        }
        self.ddb_analysis_dumps += 1;
        let ctx = calc_alg_context.process_context();
        let onto = calc_alg_context.ontology_arenas();
        let mut it = clash;
        let mut parts: Vec<String> = Vec::new();
        let mut n = 0;
        while it.is_some() && n < 16 {
            let cd = ctx.clash_desc(it);
            match cd.kind {
                super::super::process::descriptor::ClashDescriptorKind::Concept {
                    concept_descriptor,
                    individual_node,
                } => {
                    if concept_descriptor.is_some() {
                        let des = ctx.con_desc(concept_descriptor);
                        let tag = onto.concept(des.get_concept()).get_concept_tag();
                        let node_id = if individual_node.is_some() {
                            ctx.node(individual_node).individual_node_id()
                        } else {
                            -1
                        };
                        // provenance: the descriptor's own dependency track
                        // point and its branch node's branching level — a
                        // level-0 tp on a branch-dependent concept is the
                        // wrong-root-cancel smoking gun.
                        let des_tp = des.get_dependency_track_point();
                        let lvl = if des_tp.is_some() {
                            let bn = ctx.track_point(des_tp).get_branch_node();
                            if bn.is_some() {
                                ctx.branch_node(bn).get_branching_level()
                            } else {
                                -1
                            }
                        } else {
                            -2
                        };
                        parts.push(format!(
                            "{}{}@n{}[tp={:?} lvl={}]",
                            if des.is_negated() { "¬" } else { "" },
                            tag,
                            node_id,
                            des_tp,
                            lvl
                        ));
                    } else {
                        parts.push("concept(NONE)".into());
                    }
                }
                _ => parts.push(format!("{:?}-kind", cd.dep_track_point)),
            }
            it = cd.next;
            n += 1;
        }
        eprintln!(
            "FINAL-CLASH[{how}] backtracks={} bp_depth={}: {}",
            self.or_backtrack_count,
            self.or_branch_stack.len(),
            parts.join(" ")
        );
        // KM_BRIDGE_DUMP_DEP_CHAIN: additionally walk each clash descriptor's
        // dependency graph (tp → dep node → prev/additional tps) so a taint
        // loss (a branch-dependent derivation whose chain bottoms out at tag 0
        // without passing a non-deterministic node) is visible directly.
        if std::env::var_os("KM_BRIDGE_DUMP_DEP_CHAIN").is_some() {
            let mut it2 = clash;
            let mut n2 = 0;
            while it2.is_some() && n2 < 4 {
                let (des_tp, kind_str) = {
                    let cd = ctx.clash_desc(it2);
                    match cd.kind {
                        super::super::process::descriptor::ClashDescriptorKind::Concept {
                            concept_descriptor,
                            ..
                        } if concept_descriptor.is_some() => (
                            ctx.con_desc(concept_descriptor).get_dependency_track_point(),
                            "concept",
                        ),
                        _ => (cd.dep_track_point, "other"),
                    }
                };
                eprintln!("DEP-CHAIN[{n2}] ({kind_str}):");
                let mut stack: Vec<(TrackPointId, usize)> = vec![(des_tp, 1)];
                let mut seen: std::collections::HashSet<usize> = Default::default();
                let mut lines = 0;
                while let Some((t, d)) = stack.pop() {
                    if t.is_none() || lines > 48 || d > 14 {
                        continue;
                    }
                    if !seen.insert(t.index()) {
                        continue;
                    }
                    lines += 1;
                    let tpr = ctx.track_point(t);
                    let dn = tpr.dependency_node();
                    if dn.is_none() {
                        eprintln!("{:indent$}tp#{} tag={} (BASE)", "", t.index(), tpr.process_tag, indent = d * 2);
                        continue;
                    }
                    let node = ctx.dep_node(dn);
                    let base = node.base();
                    eprintln!(
                        "{:indent$}tp#{} tag={} node={:?} nondet={}",
                        "",
                        t.index(),
                        tpr.process_tag,
                        node.kind(),
                        node.kind().is_non_deterministic(),
                        indent = d * 2
                    );
                    stack.push((base.dep_track_point, d + 1));
                    let mut al = base.additional_after;
                    while al.is_some() {
                        stack.push((ctx.dep_link(al).dep_track_point, d + 1));
                        al = ctx.dep_link(al).next;
                    }
                }
                it2 = ctx.clash_desc(it2).next;
                n2 += 1;
            }
        }
    }

    /// Deterministic singleton-concept merge rule — the bridge's realisation
    /// of the clausal datatype value-identity `C(x) ∧ C(y) → x = y` (a
    /// role-free eq-head clause; Konclude never sees this shape because its
    /// databox literal handling gives value identity natively). Scans the
    /// live nodes for two distinct positive carriers of a singleton concept
    /// and merges the later into the earlier (the u08 min-id refinement),
    /// under a SameIndividualsMerge dependency joining BOTH carriers'
    /// concept-descriptor track points — faithful DDB provenance (a NONE or
    /// base track point here would repaint branch-dependent merges as
    /// independent: the u08 wrong-root-cancel class). Returns true when a
    /// merge happened (the caller re-drives before claiming fixpoint).
    fn ht_apply_singleton_merges(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut merged_any = false;
        let singleton_concepts = self.singleton_concepts.clone(); // tiny (distinct literal values)
        for &concept in &singleton_concepts {
            loop {
                // Collect the first two LIVE positive carriers (read-only
                // label access: skip nodes with no materialised label set —
                // never allocate during the scan).
                let mut first: Option<(NodeId, TrackPointId)> = None;
                let mut second: Option<(NodeId, TrackPointId)> = None;
                {
                    let ctx = calc_alg_context.process_context();
                    let onto = calc_alg_context.ontology_arenas();
                    let con_tag = onto.concept(concept).get_concept_tag();
                    let n = ctx.node_count();
                    for i in 0..n {
                        // skip PHANTOM nodes (created by refuted alternatives,
                        // lingering in the arena under chronological no-COW
                        // backtracking — dead state, never merge with them)
                        if self
                            .phantom_node_intervals
                            .iter()
                            .any(|&(a, b)| i >= a && i < b)
                        {
                            continue;
                        }
                        let node_id: NodeId = Id::new(i as Cint64);
                        let node = ctx.node(node_id);
                        // skip nodes already merged away
                        if node.has_merged_into_individual_node_id() {
                            continue;
                        }
                        let label = node.reapply_con_label_set;
                        if label.is_none() {
                            continue;
                        }
                        let mut con_des: ConDescId = Id::NONE;
                        let mut dep_track_point: TrackPointId = Id::NONE;
                        let found = ctx
                            .label_set(label)
                            .get_concept_descriptor_by_tag_in_context(
                                ctx,
                                con_tag,
                                &mut con_des,
                                &mut dep_track_point,
                            );
                        if !found || ctx.con_desc(con_des).is_negated() {
                            continue;
                        }
                        if first.is_none() {
                            first = Some((node_id, dep_track_point));
                        } else {
                            second = Some((node_id, dep_track_point));
                            break;
                        }
                    }
                }
                let (Some((into, into_tp)), Some((from, from_tp))) = (first, second) else {
                    break; // zero or one carrier: this concept is done
                };
                // KM_BRIDGE_WATCH_SINGLETON: provenance for every singleton
                // merge (phantom-merge hunts: a `from`/`into` node id that was
                // created by an ABANDONED alternative marks the cross-branch
                // pollution case).
                if std::env::var_os("KM_BRIDGE_WATCH_SINGLETON").is_some() {
                    let ctx = calc_alg_context.process_context();
                    eprintln!(
                        "SINGLETON-MERGE tag={} into=#{}(indi {}) from=#{}(indi {}) bp_depth={} backtracks={}",
                        calc_alg_context
                            .ontology_arenas()
                            .concept(concept)
                            .get_concept_tag(),
                        into.raw,
                        ctx.node(into).individual_node_id(),
                        from.raw,
                        ctx.node(from).individual_node_id(),
                        self.or_branch_stack.len(),
                        self.or_backtrack_count,
                    );
                }
                let mut merge_dep_track_point: TrackPointId = Id::NONE;
                let mut into_mut = into;
                self.create_same_individual_merge_dependency(
                    &mut merge_dep_track_point,
                    &mut into_mut,
                    into_tp,
                    from_tp,
                    calc_alg_context,
                );
                self.merge_individual_node_into(
                    into,
                    from,
                    merge_dep_track_point,
                    calc_alg_context,
                );
                self.applied_singleton_merge_count += 1;
                merged_any = true;
                if calc_alg_context.has_pending_signal() {
                    return true; // a clash raised during the merge unwinds to the drive
                }
            }
        }
        merged_any
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
