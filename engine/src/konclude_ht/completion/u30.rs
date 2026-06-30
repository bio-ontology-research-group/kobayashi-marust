//! `completion::u30` — Clash processing family, batch (port unit #30 of 36).
//!
//! Faithful port of the 18 methods the manifest (`01-completion-methods.md`,
//! "Unit 30") groups under clash-descriptor construction, tracked-clash
//! descriptor handling and the label-concept clash tests of Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.cpp`.
//! cpp source line ranges (1-based) are noted on each item.
//!
//! Methods (cpp order):
//!   * `createClashedIndividualNodeDescriptor`                       [4395–4405]
//!   * `generateDebugTrackedClashedDescriptorSummaryString`          [6569–6585]
//!   * `generateDebugTrackedClashedDescriptorString`                 [6588–6718]
//!   * `getFreeTrackedClashedDescriptor`                             [6952–6959]
//!   * `markRelevanceForTrackedClashedDescriptors`                   [7352–7357]
//!   * `addIndiNodeSignatureOfUnsatisfiableClashedDescriptors`       [7545–7552]
//!   * `isClashedDescriptorSortedBefore`                             [7554–7556]
//!   * `getSortedClashedDescriptors`                                 [7559–7583]
//!   * `writeUnsatisfiableClashedDescriptors`                        [7586–7592]
//!   * `getCollectedFilteredClashedDescriptorsFromBranch`           [7595–7652]
//!   * `createTrackedClashesDescriptors`                            [7921–7935]
//!   * `createTrackedClashesDescriptor`                             [7939–7973]
//!   * `createClashedConceptDescriptor`                            [16717–16720]
//!   * `createClashedIndividualLinkDescriptor`                     [16722–16725]
//!   * `createClashedIndividualDistinctDescriptor`                 [16727–16730]
//!   * `createClashedNegationDisjointDescriptor`                   [16732–16735]
//!   * `isLabelConceptClashSet` (label-set / label-set)            [17323–17391]
//!   * `isLabelConceptClashSet` (node / node, builds clashes)      [20867–20932]
//!
//! KONCLUDE-PORT-NOTE[ownership]: each method is a member of
//! `CCalculationTableauCompletionTaskHandleAlgorithm`, so it becomes `&mut self`
//! plus the threaded per-thread context `calc_alg_context: &mut
//! CalculationAlgorithmContextBase`. C++ `CIndividualProcessNode*&` in/out
//! pointer-references become `&mut NodeId`; a plain value `CIndividualProcessNode*`
//! becomes `NodeId`; `CConceptDescriptor*` → `ConDescId`; `CClashedDependencyDescriptor*`
//! → `ClashDescId`; `CDependencyTrackPoint*` → `TrackPointId`; the edge value
//! params → `EdgeId` / `DistinctEdgeId` / `DisjointEdgeId`; the
//! `CNonDeterministicDependencyNode*` branch node → `DependencyId`. The per-test
//! arenas are reached through the context (`calc_alg_context.process_context()` /
//! `_mut()`), the databox as `calc_alg_context.processing_data_box{,_mut}()`.
//!
//! Deferral landscape. Two subsystems gate the bulk of this unit:
//!   * `CTrackedClashedDescriptor` + the stack-local `CTrackedClashedDependencyLine`
//!     are NOT yet ported (a tracking-line record with no arena, plus the
//!     `CTrackedClashedDescriptor` subclass of `CClashedDependencyDescriptor` whose
//!     extra appropriated-individual / branching-level-tag / variable-binding-path
//!     payload has no struct yet). Per the established struct-wave convention
//!     (see u29) these appear as opaque `Cint64` handles; the methods whose whole
//!     body is the tracked-clash linked-list manipulation (debug strings, free-list
//!     pop, relevance marking, insertion sort, the branch-filtered collection, and
//!     the two `createTrackedClashesDescriptor*` builders) are kept `// PORT-PENDING`
//!     with a faithful structural transcription of the C++.
//!   * the `CClashedDependencyFactory` (`used_clash_descriptor_factory`, a zero-size
//!     `Id` stub) — every `createClashed*Descriptor` wrapper bottoms out in one
//!     `factory->createClashed*Descriptor(...)` call (`W6-DEFER[api]`); the wrapper
//!     shape + chain handoff are ported.
//!
//! Fully ported here (concrete arena resolution): the `createClashedIndividualNodeDescriptor`
//! adding-sorted concept-descriptor walk (only the LS-1-deferred chain-head getter
//! stays a stub), the four `createClashed*Descriptor` factory wrappers, the null-
//! handler guard of `writeUnsatisfiableClashedDescriptors`, and — mirroring the
//! u16/u34 label-set comparison ports — the count/threshold branch selection plus
//! the node-version label-set fetch+swap of the two `isLabelConceptClashSet`
//! methods (the per-concept iterator walks are `CReapplyConceptLabelSetIterator`,
//! an unported LS-1 stub, so they stay `W6-DEFER[api]` with logic in-comment).
//! Logic is documented, never silently dropped.

#![allow(dead_code)]
#![allow(unused_variables)]

use super::super::model::substrate::{Cint64, Id};
use super::super::process::{
    ClashDescId, ConDescId, DependencyId, DisjointEdgeId, DistinctEdgeId, EdgeId, LabelSetId,
    NodeId, TrackPointId,
};
use super::context::CalculationAlgorithmContextBase;

impl super::algorithm::CompletionTaskHandleAlgorithm {
    // =======================================================================
    // Clash-descriptor construction from a node's label set (cpp 4395–4405).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::createClashedIndividualNodeDescriptor`.
    /// cpp 4395–4405.
    ///
    /// Walks the node's adding-sorted concept-descriptor chain and prepends one
    /// clashed-concept descriptor per concept onto `prev_clashes`, returning the new
    /// chain head.
    pub fn create_clashed_individual_node_descriptor(
        &mut self,
        prev_clashes: ClashDescId,
        process_indi: &mut NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> ClashDescId {
        // CClashedDependencyDescriptor* clashDes = prevClashes;
        // CReapplyConceptLabelSet* conSet = processIndi->getReapplyConceptLabelSet(false);
        // CConceptDescriptor* conDesIt = conSet->getAddingSortedConceptDescriptionLinker();
        // while (conDesIt) {
        //   CConceptDescriptor* conDes = conDesIt;
        //   clashDes = createClashedConceptDescriptor(clashDes,processIndi,conDes,conDes->getDependencyTrackPoint(),ctx);
        //   conDesIt = conDesIt->getNext();
        // }
        // return clashDes;
        let mut clash_des = prev_clashes;
        let _con_set: LabelSetId = calc_alg_context
            .process_context_mut()
            .node_mut(*process_indi)
            .get_reapply_concept_label_set(false);
        // W6-DEFER[api]: `CReapplyConceptLabelSet::getAddingSortedConceptDescriptionLinker`
        // is not yet ported (LS-1 defer note in `process/satellites.rs`); the
        // adding-sorted concept-descriptor chain head resolves to `Id::NONE` until it
        // lands, so the faithful walk below is structurally correct but inert this
        // wave (the `get_next_concept_descriptor` advance + `create_clashed_concept_descriptor`
        // prepend are concrete).
        let mut con_des_it: ConDescId = Id::NONE; // = conSet->getAddingSortedConceptDescriptionLinker()
        while con_des_it.is_some() {
            let con_des = con_des_it;
            let prev_dep_track_point = calc_alg_context
                .process_context()
                .con_desc(con_des)
                .get_dependency_track_point();
            clash_des = self.create_clashed_concept_descriptor(
                clash_des,
                process_indi,
                con_des,
                prev_dep_track_point,
                calc_alg_context,
            );
            con_des_it = calc_alg_context
                .process_context()
                .con_desc(con_des_it)
                .get_next_concept_descriptor();
        }
        clash_des
    }

    // =======================================================================
    // Debug tracked-clash descriptor strings (cpp 6569–6718).
    // Both are instrumentation over the opaque `CTrackedClashedDescriptor` chain.
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::generateDebugTrackedClashedDescriptorSummaryString`.
    /// cpp 6569–6585.
    ///
    /// KONCLUDE-PORT-NOTE[api]: debug-only string builder over the not-yet-ported
    /// opaque `CTrackedClashedDescriptor` chain (`Cint64`).
    pub fn generate_debug_tracked_clashed_descriptor_summary_string(
        &mut self,
        tracked_clash_descriptors: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> String {
        // PORT-PENDING: faithful transcription of cpp 6569–6585. Outline:
        //   clashString = "";
        //   for it = trackedClashDescriptors; it; it = it->getNextDescriptor():
        //     conDes = it->getConceptDescriptor();
        //     conceptString = conDes ? CConceptTextFormater::getConceptString(conDes->getConcept(), conDes->isNegated()) : "null";
        //     if !clashString.isEmpty(): clashString += ", ";
        //     clashString += conceptString;
        //   return clashString;
        //
        // Held PORT-PENDING: the opaque `CTrackedClashedDescriptor` linked-list
        // (`getNextDescriptor` / `getConceptDescriptor`) and the
        // `CConceptTextFormater` debug formatter are not yet ported (W3-DEFER[api]).
        let _ = (tracked_clash_descriptors, calc_alg_context);
        String::new()
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::generateDebugTrackedClashedDescriptorString`.
    /// cpp 6588–6718.
    ///
    /// KONCLUDE-PORT-NOTE[api]: debug-only multi-line string builder over the opaque
    /// `CTrackedClashedDescriptor` chain; the body is a large dependency-type → label
    /// switch.
    pub fn generate_debug_tracked_clashed_descriptor_string(
        &mut self,
        tracked_clash_descriptors: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> String {
        // PORT-PENDING: faithful transcription of cpp 6588–6718. Outline:
        //   clashListString = "";
        //   for it = trackedClashDescriptors; it; it = it->getNextDescriptor():
        //     conDes = it->getConceptDescriptor();
        //     conceptString = conDes ? getConceptString(conDes->getConcept(), conDes->isNegated()) : "null";
        //     depTrackPoint = it->getDependencyTrackPoint();
        //     dependencyString = "null";
        //     if depTrackPoint:
        //       depNode = depTrackPoint->getDependencyNode();
        //       depTypeString = switch(depNode->getDependencyType()) {  // DependencyNode::DNT* -> label
        //         DNTINDEPENDENTBASE->"INDEPENDENT", DNTALLDEPENDENCY->"ALL", DNTSOMEDEPENDENCY->"SOME",
        //         DNTANDDEPENDENCY->"AND", DNTORDEPENDENCY->"OR", DNTATLEASTDEPENDENCY->"ATLEAST",
        //         DNTAUTOMATCHOOSEDEPENDENCY->"AUTOMATCHOOSE", DNTAUTOMATTRANSACTIONDEPENDENCY->"AUTOMATTRANSACTION",
        //         DNTSELFDEPENDENCY->"SELF", DNTVALUEDEPENDENCY->"VALUE", DNTNEGVALUEDEPENDENCY->"NEGVALUE",
        //         DNTDISTINCTDEPENDENCY->"DISTINCT", DNTMERGEDCONCEPT->"MERGEDCONCEPT", DNTMERGEDLINK->"MERGEDLINK",
        //         DNTMERGEDEPENDENCY->"MERGE", DNTATMOSTDEPENDENCY->"ATMOST", DNTQUALIFYDEPENDENCY->"QUALIFY",
        //         DNTFUNCTIONALDEPENDENCY->"FUNCTIONAL", DNTNOMINALDEPENDENCY->"NOMINAL",
        //         DNTIMPLICATIONDEPENDENCY->"IMPLICATION", DNTEXPANDEDDEPENDENCY->"EXPANDED",
        //         DNTDATATYPETRIGGERDEPENDENCY->"DATATYPETRIGGER" };
        //       depNodeConDes = depNode->getConceptDescriptor();
        //       conceptDepNodeString = depNodeConDes ? getConceptString(depNodeConDes->getConcept(), depNodeConDes->isNegated()) : "null";
        //       depInfoString = "";
        //       if depNode->isNonDeterministiDependencyNode():
        //         nonDetDepNode = (CNonDeterministicDependencyNode*)depNode;
        //         depInfoString += " NonDetDep, <openedDependencyTrackingPointsCount / branchTrackPoints.count>";
        //       depInfoString += " + ...(getAdditionalDependencyCount)";
        //       dependencyString = "{depTypeString}-Dependency: {conceptDepNodeString}{depInfoString}";
        //     clashString = "\t[ID:appropriatedIndividualID / L:appropriatedIndividualLevel | B:branchingLevelTag]: {conceptString}  -->  dependencyString\r\n";
        //     clashListString += clashString;
        //   clashListString.replace("\r\n","<br>");
        //   return clashListString;
        //
        // Held PORT-PENDING: the opaque `CTrackedClashedDescriptor` chain, the
        // `CDependencyNode`/`CNonDeterministicDependencyNode` debug accessors, and the
        // `CConceptTextFormater` formatter (W3-DEFER[api]).
        let _ = (tracked_clash_descriptors, calc_alg_context);
        String::new()
    }

    // =======================================================================
    // Tracked-clash free-list pop (cpp 6952–6959).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::getFreeTrackedClashedDescriptor`.
    /// cpp 6952–6959.
    ///
    /// KONCLUDE-PORT-NOTE[api]: `CTrackedClashedDependencyLine` (stack-local, no
    /// arena yet) and `CTrackedClashedDescriptor` are unported → opaque `Cint64`.
    pub fn get_free_tracked_clashed_descriptor(
        &mut self,
        tracking_line: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> Cint64 {
        // PORT-PENDING: faithful transcription of cpp 6952–6959. Outline:
        //   des = trackingLine->takeNextFreeTrackedClashedDescriptor();
        //   if !des:
        //     tmpMemMan = calcAlgContext->getUsedTemporaryMemoryAllocationManager();
        //     des = CObjectAllocator<CTrackedClashedDescriptor>::allocateAndConstruct(tmpMemMan);
        //   return des;
        //
        // Held PORT-PENDING: the tracking-line free-list (`takeNextFreeTrackedClashedDescriptor`)
        // and the temporary-memory bump allocation of a fresh `CTrackedClashedDescriptor`
        // ([memory-pool]) are not yet ported (W3-DEFER[api]).
        let _ = (tracking_line, calc_alg_context);
        0
    }

    // =======================================================================
    // Relevance marking over a tracked-clash chain (cpp 7352–7357).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::markRelevanceForTrackedClashedDescriptors`.
    /// cpp 7352–7357.
    ///
    /// Marks dependency relevance for the track point of every tracked-clash
    /// descriptor in the chain.
    pub fn mark_relevance_for_tracked_clashed_descriptors(
        &mut self,
        descriptors: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // PORT-PENDING: faithful transcription of cpp 7352–7357. Outline:
        //   for desIt = descriptors; desIt; desIt = desIt->getNextDescriptor():
        //     depTrackPoint = desIt->getDependencyTrackPoint();
        //     markDependencyRelevance(depTrackPoint, ctx);   // dependency-tracking unit
        //
        // Held PORT-PENDING: iteration over the opaque `CTrackedClashedDescriptor`
        // chain. The per-descriptor `markDependencyRelevance` sibling (dependency-
        // tracking unit) becomes live once the tracked-clash record is ported
        // (W3-DEFER[api]).
        let _ = (descriptors, calc_alg_context);
    }

    // =======================================================================
    // Unsat-caching signature collection (cpp 7545–7552).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addIndiNodeSignatureOfUnsatisfiableClashedDescriptors`.
    /// cpp 7545–7552.
    ///
    /// Inserts the concept-signature value of the (corrected nominal) individual
    /// addressed by the tracked-clash descriptor into `mUnsatCachingSignatureSet`.
    pub fn add_indi_node_signature_of_unsatisfiable_clashed_descriptors(
        &mut self,
        tracked_clashed_des: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // cint64 indiID = trackedClashedDes->getAppropriatedIndividualID();
        // CIndividualProcessNode* indi = getCorrectedNominalIndividualNode(indiID, ctx);
        // CReapplyConceptLabelSet* conSet = indi->getReapplyConceptLabelSet(false);
        // cint64 conSig = conSet->getConceptSignatureValue();
        // mUnsatCachingSignatureSet.insert(conSig);
        // return true;
        //
        // W3-DEFER[api]: `getAppropriatedIndividualID()` reads the opaque (not-yet-
        // ported) `CTrackedClashedDescriptor`; once that record lands the resolvable
        // tail runs against concrete accessors:
        //   let indi = self.get_corrected_nominal_individual_node(indi_id, calc_alg_context); // u16
        //   let con_set = calc_alg_context.process_context_mut().node_mut(indi)
        //                     .get_reapply_concept_label_set(false);
        //   let con_sig = calc_alg_context.process_context().label_set(con_set)
        //                     .get_concept_signature_value();
        //   self.unsat_caching_signature_set.insert(con_sig);
        let _ = (tracked_clashed_des, calc_alg_context);
        true
    }

    // =======================================================================
    // Tracked-clash sort predicate + insertion sort (cpp 7554–7583).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::isClashedDescriptorSortedBefore`.
    /// cpp 7554–7556.
    ///
    /// True iff `before`'s concept tag does not exceed `after`'s (or `after` is the
    /// chain end).
    pub fn is_clashed_descriptor_sorted_before(
        &mut self,
        tracked_clashed_des_before: Cint64,
        tracked_clashed_des_after: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // return !trackedClashedDesAfter
        //        || trackedClashedDesBefore->getConceptDescriptor()->getConceptTag()
        //           <= trackedClashedDesAfter->getConceptDescriptor()->getConceptTag();
        //
        // W3-DEFER[api]: `CTrackedClashedDescriptor::getConceptDescriptor()` +
        // `CConceptDescriptor::getConceptTag()` over the opaque tracked-clash record.
        // The `!after` early-true (chain-end) arm is the resolvable part: an empty
        // `after` handle (`0`) sorts `before` first.
        if tracked_clashed_des_after == 0 {
            return true;
        }
        let _ = (tracked_clashed_des_before, calc_alg_context);
        true
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::getSortedClashedDescriptors`.
    /// cpp 7559–7583.
    ///
    /// Insertion-sorts the tracked-clash chain by concept tag (via
    /// `isClashedDescriptorSortedBefore`), returning the new sorted head.
    pub fn get_sorted_clashed_descriptors(
        &mut self,
        tracked_clashed_des: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> Cint64 {
        // PORT-PENDING: faithful transcription of cpp 7559–7583. Outline:
        //   sortedTrackedClashedDes = trackedClashedDes;
        //   trackedClashedDes = trackedClashedDes->getNextDescriptor();
        //   sortedTrackedClashedDes->clearNext();
        //   while trackedClashedDes:
        //     tmp = trackedClashedDes; trackedClashedDes = trackedClashedDes->getNextDescriptor(); tmp->clearNext();
        //     if isClashedDescriptorSortedBefore(tmp, sortedTrackedClashedDes, ctx):
        //       sortedTrackedClashedDes = tmp->append(sortedTrackedClashedDes);
        //     else:
        //       for insertPosIt = sortedTrackedClashedDes; insertPosIt; insertPosIt = nextSortedPosDes:
        //         nextSortedPosDes = insertPosIt->getNextDescriptor();
        //         if isClashedDescriptorSortedBefore(tmp, nextSortedPosDes, ctx):
        //           insertPosIt->insertNext(tmp); break;
        //   return sortedTrackedClashedDes;
        //
        // Held PORT-PENDING: the opaque `CTrackedClashedDescriptor` chain ops
        // (`getNextDescriptor` / `clearNext` / `append` / `insertNext`); the
        // `isClashedDescriptorSortedBefore` predicate (this unit) is the comparator
        // (W3-DEFER[api]).
        let _ = (tracked_clashed_des, calc_alg_context);
        tracked_clashed_des
    }

    // =======================================================================
    // Unsat-cache write (cpp 7586–7592).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::writeUnsatisfiableClashedDescriptors`.
    /// cpp 7586–7592.
    ///
    /// Forwards the tracked-clash chain to the unsatisfiable-cache handler when one
    /// is installed; returns false otherwise.
    pub fn write_unsatisfiable_clashed_descriptors(
        &mut self,
        tracked_clashed_des: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // CUnsatisfiableCacheHandler* unsatCacheHandler = calcAlgContext->getUsedUnsatisfiableCacheHandler();
        // if (unsatCacheHandler) return unsatCacheHandler->writeUnsatisfiableClashedDescriptors(trackedClashedDes, ctx);
        // return false;
        //
        // W6-DEFER[api]: the `CUnsatisfiableCacheHandler` (Cache subtree, not yet
        // ported) is reached via `getUsedUnsatisfiableCacheHandler()`; when present it
        // writes the (opaque) tracked-clash chain into the unsat cache. The handler is
        // absent this wave, so the guarded forward yields the null-handler path
        // (false), faithfully.
        let _ = (tracked_clashed_des, calc_alg_context);
        false
    }

    // =======================================================================
    // Branch-filtered tracked-clash collection (cpp 7595–7652).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::getCollectedFilteredClashedDescriptorsFromBranch`.
    /// cpp 7595–7652.
    ///
    /// Collects (de-duplicated) the tracked-clash descriptors of a non-deterministic
    /// branch: walks every branch track point, turning each non-self-pointing clash
    /// into a tracked-clash descriptor (one per dependency), records the involved
    /// individuals on the tracking line, then appends the deterministic backtracking
    /// of the self-pointing clash.
    ///
    /// KONCLUDE-PORT-NOTE[api]: `CNonDeterministicDependencyNode*` → `DependencyId`;
    /// the tracking line, the `CTrackedClashedDescriptor` chain, the
    /// `CTrackedClashedDescriptorHasher` `PROCESSINGSET`, and the temporary memory
    /// allocation manager are opaque `Cint64` this wave. `CClashedDependencyDescriptor*`
    /// IS ported (`ClashDescId`).
    pub fn get_collected_filtered_clashed_descriptors_from_branch(
        &mut self,
        non_det_clashed_pointing_des: Cint64,
        non_det_branch_dep_node: DependencyId,
        tracking_line: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
        tmp_mem_man: Cint64,
    ) -> Cint64 {
        // PORT-PENDING: faithful transcription of cpp 7595–7652. Outline:
        //   testClashedSet = CPROCESSINGSET<CTrackedClashedDescriptorHasher>(ctx->getUsedTaskProcessorContext());
        //   trackPointIt = nonDetBranchDepNode->getBranchTrackPoints();
        //   newTrackedClashedDescriptorList = nullptr;
        //   nonDetPointingFirstTrackedClashedDescriptor = nonDetClashedPointingDes;
        //   while trackPointIt:
        //     clashedDepDescriptors = trackPointIt->getClashes();
        //     for clashedDepDescriptor in clashedDepDescriptors:
        //       if clashedDepDescriptor->getDependencyTrackPoint()->getDependencyNode() != nonDetBranchDepNode:
        //         net = createTrackedClashesDescriptor(clashedDepDescriptor, ctx, tmpMemMan);   // this unit (default copy)
        //         hasher = CTrackedClashedDescriptorHasher(net);
        //         if !testClashedSet.contains(hasher): testClashedSet.insert(hasher); newList = net->append(newList);
        //       else:
        //         if !nonDetPointingFirstTrackedClashedDescriptor:
        //           nonDetPointingFirstTrackedClashedDescriptor = createTrackedClashesDescriptor(clashedDepDescriptor, ctx, tmpMemMan);
        //     for involvedIndiIdLinkerIt in trackPointIt->getInvolvedIndividualIdsLinker():
        //       trackingLine->addInvolvedIndividual(involvedIndiIdLinkerIt->getData());
        //     trackPointIt = trackPointIt->getNext();
        //   KONCLUDE_ASSERT_X(nonDetPointingFirstTrackedClashedDescriptor, ...);
        //   nonDetBacktrackedClashedDes = getBacktrackedDeterministicClashedDescriptors(   // u29
        //       nonDetPointingFirstTrackedClashedDescriptor, trackingLine, nullptr, ctx);
        //   for it = nonDetBacktrackedClashedDes; it; (advance+clearNext):
        //     hasher = CTrackedClashedDescriptorHasher(it);
        //     if !testClashedSet.contains(hasher): testClashedSet.insert(hasher); newList = it->append(newList);
        //   return newTrackedClashedDescriptorList;
        //
        // Held PORT-PENDING: every typed local is gated by the unported tracked-clash
        // record / hasher set / tracking line; `CNonDeterministicDependencyTrackPoint`
        // (`getClashes` / `getInvolvedIndividualIdsLinker`) is the dependency-spine
        // branch track point (its `getBranchTrackPoints` accessor on the dependency
        // node is the entry). `createTrackedClashesDescriptor` (this unit) and
        // `getBacktrackedDeterministicClashedDescriptors` (u29) become live once the
        // tracked-clash record is ported (W3-DEFER[api]).
        let _ = (
            non_det_clashed_pointing_des,
            non_det_branch_dep_node,
            tracking_line,
            calc_alg_context,
            tmp_mem_man,
        );
        0
    }

    // =======================================================================
    // Tracked-clash descriptor builders (cpp 7921–7973).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::createTrackedClashesDescriptors`.
    /// cpp 7921–7935.
    ///
    /// Builds the tracked-clash chain for an entire `CClashedDependencyDescriptor`
    /// list (one tracked-clash descriptor per clash, head-prepended).
    ///
    /// KONCLUDE-PORT-NOTE[overload]: the C++ trailing `copyIndependentConceptDescriptors`
    /// has a header default; callers that pass three args (e.g. the branch collector)
    /// supply the default — the Rust port keeps it explicit.
    pub fn create_tracked_clashes_descriptors(
        &mut self,
        clashes: ClashDescId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
        tmp_mem_man: Cint64,
        copy_independent_concept_descriptors: bool,
    ) -> Cint64 {
        // PORT-PENDING: faithful transcription of cpp 7921–7935. Outline:
        //   if !tmpMemMan: tmpMemMan = calcAlgContext->getUsedTemporaryMemoryAllocationManager();
        //   trackingClashes = nullptr;
        //   for nextClash = clashes; nextClash; nextClash = nextClash->getNext():
        //     newTrackingClash = createTrackedClashesDescriptor(nextClash, ctx, tmpMemMan, copyIndependentConceptDescriptors);
        //     trackingClashes = newTrackingClash->append(trackingClashes);
        //   return trackingClashes;
        //
        // The `ClashDescId` walk + `get_next` advance are concrete, but each produced
        // element is an opaque `CTrackedClashedDescriptor` (unported) and the chain is
        // assembled by its `append`; held PORT-PENDING until the tracked-clash record
        // lands (W3-DEFER[api]). `createTrackedClashesDescriptor` is this unit.
        let _ = (
            clashes,
            calc_alg_context,
            tmp_mem_man,
            copy_independent_concept_descriptors,
        );
        0
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::createTrackedClashesDescriptor`.
    /// cpp 7939–7973.
    ///
    /// Builds one tracked-clash descriptor from a single `CClashedDependencyDescriptor`,
    /// dispatching on its runtime subclass (already-tracked / clashed-concept /
    /// clashed-datatype-value-space-exclusion / generic-by-dependency).
    ///
    /// KONCLUDE-PORT-NOTE[api]: the C++ `dynamic_cast` over the
    /// `CClashedDependencyDescriptor` hierarchy cannot be reproduced — `ClashDescriptor`
    /// is currently a single struct (its per-subclass payload + the
    /// `CTrackedClashedDescriptor` subtype are deferred to the clash tagged-enum unit),
    /// so the four-way dispatch is held PORT-PENDING.
    pub fn create_tracked_clashes_descriptor(
        &mut self,
        clash_des: ClashDescId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
        tmp_mem_man: Cint64,
        copy_independent_concept_descriptors: bool,
    ) -> Cint64 {
        // PORT-PENDING: faithful transcription of cpp 7939–7973. Outline:
        //   if !tmpMemMan: tmpMemMan = calcAlgContext->getUsedTemporaryMemoryAllocationManager();
        //   newTrackingClash = nullptr;
        //   clashedTrackDes = dynamic_cast<CTrackedClashedDescriptor*>(clashDes);
        //   if clashedTrackDes:                                    // already a tracked clash
        //     newTrackingClash = alloc CTrackedClashedDescriptor;
        //     newTrackingClash->initTrackedClashedDescriptor(clashedTrackDes);
        //     if newTrackingClash->isPointingToIndependentDependencyNode()
        //        && copyIndependentConceptDescriptors && newTrackingClash->getConceptDescriptor():
        //       conDes = newTrackingClash->getConceptDescriptor();
        //       conDesCopy = alloc CConceptDescriptor;
        //       conDesCopy->initConceptDescriptor(conDes->getConcept(), conDes->isNegated(), conDes->getDependencyTrackPoint());
        //       newTrackingClash->setConceptDescriptor(conDesCopy);
        //   else:
        //     clashedConDes = dynamic_cast<CClashedConceptDescriptor*>(clashDes);
        //     if clashedConDes:                                    // concept clash
        //       newTrackingClash = alloc CTrackedClashedDescriptor;
        //       newTrackingClash->initTrackedClashedDescriptor(clashedConDes->getAppropriatedIndividual(),
        //           clashedConDes->getConceptDescriptor(), nullptr, clashedConDes->getDependencyTrackPoint());
        //     else:
        //       clashedDataVSExDes = dynamic_cast<CClashedDatatypeValueSpaceExclusionDescriptor*>(clashDes);
        //       if clashedDataVSExDes:                             // datatype value-space exclusion clash
        //         newTrackingClash = alloc CTrackedClashedDescriptor;
        //         newTrackingClash->initTrackedClashedDescriptor(clashedDataVSExDes->getAppropriatedIndividual(),
        //             nullptr, nullptr, clashedDataVSExDes->getDependencyTrackPoint());
        //       else:                                              // generic: resolve node from dependency
        //         indiNode = getCoresspondingIndividualNodeFromDependency(clashDes->getDependencyTrackPoint(), ctx); // u28
        //         newTrackingClash = alloc CTrackedClashedDescriptor;
        //         newTrackingClash->initTrackedClashedDescriptor(indiNode, nullptr, nullptr, clashDes->getDependencyTrackPoint());
        //   return newTrackingClash;
        //
        // Held PORT-PENDING: the `dynamic_cast` subclass dispatch (clash tagged-enum
        // unit), the opaque `CTrackedClashedDescriptor` alloc + init, the independent-
        // concept-descriptor copy ([memory-pool]), and `getCoresspondingIndividualNodeFromDependency`
        // (u28) (W3-DEFER[api]).
        let _ = (
            clash_des,
            calc_alg_context,
            tmp_mem_man,
            copy_independent_concept_descriptors,
        );
        0
    }

    // =======================================================================
    // Clash-descriptor factory wrappers (cpp 16717–16735).
    //
    // Each is the identical Konclude idiom:
    //   CClashedDependencyDescriptor* clashDes =
    //       calcAlgContext->getClashDescriptorFactory()->createClashed*Descriptor(prevClashes, ..., ctx);
    //   return clashDes;
    // W6-DEFER[api]: the `CClashedDependencyFactory` (`used_clash_descriptor_factory`,
    // a zero-size `Id` stub) is not yet ported; the factory prepend of a fresh
    // clash descriptor onto `prevClashes` is deferred. Returning the unchanged chain
    // head keeps the descriptor list valid this wave.
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::createClashedConceptDescriptor`.
    /// cpp 16717–16720.
    pub fn create_clashed_concept_descriptor(
        &mut self,
        prev_clashes: ClashDescId,
        process_indi: &mut NodeId,
        con_des: ConDescId,
        prev_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> ClashDescId {
        let clash_des = prev_clashes;
        // W6-DEFER[api]: clash_des = calc_alg_context.clash_descriptor_factory()
        //     .create_clashed_concept_descriptor(prev_clashes, process_indi, con_des, prev_dep_track_point, ctx);
        let _ = (process_indi, con_des, prev_dep_track_point, calc_alg_context);
        clash_des
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::createClashedIndividualLinkDescriptor`.
    /// cpp 16722–16725.
    pub fn create_clashed_individual_link_descriptor(
        &mut self,
        prev_clashes: ClashDescId,
        link: EdgeId,
        prev_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> ClashDescId {
        let clash_des = prev_clashes;
        // W6-DEFER[api]: clash_des = factory.create_clashed_individual_link_descriptor(
        //     prev_clashes, link, prev_dep_track_point, ctx);
        let _ = (link, prev_dep_track_point, calc_alg_context);
        clash_des
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::createClashedIndividualDistinctDescriptor`.
    /// cpp 16727–16730.
    pub fn create_clashed_individual_distinct_descriptor(
        &mut self,
        prev_clashes: ClashDescId,
        distinct: DistinctEdgeId,
        prev_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> ClashDescId {
        let clash_des = prev_clashes;
        // W6-DEFER[api]: clash_des = factory.create_clashed_individual_distinct_descriptor(
        //     prev_clashes, distinct, prev_dep_track_point, ctx);
        let _ = (distinct, prev_dep_track_point, calc_alg_context);
        clash_des
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::createClashedNegationDisjointDescriptor`.
    /// cpp 16732–16735.
    pub fn create_clashed_negation_disjoint_descriptor(
        &mut self,
        prev_clashes: ClashDescId,
        disjoint_neg_link: DisjointEdgeId,
        prev_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> ClashDescId {
        let clash_des = prev_clashes;
        // W6-DEFER[api]: clash_des = factory.create_clashed_negation_disjoint_descriptor(
        //     prev_clashes, disjoint_neg_link, prev_dep_track_point, ctx);
        let _ = (disjoint_neg_link, prev_dep_track_point, calc_alg_context);
        clash_des
    }

    // =======================================================================
    // Label-concept clash tests (cpp 17323–17391 and 20867–20932).
    //
    // Mirrors the u16/u34 label-set comparison ports: the count/threshold branch
    // selection (and, for the node version, the label-set fetch + count-swap) is
    // ported against concrete accessors; the per-concept lockstep walks iterate
    // `CReapplyConceptLabelSetIterator`, an unported LS-1 stub, so they stay
    // `W6-DEFER[api]` with the faithful logic in-comment.
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::isLabelConceptClashSet`
    /// (label-set / label-set form). cpp 17323–17391.
    ///
    /// KONCLUDE-PORT-NOTE[overload]: C++ overloads `isLabelConceptClashSet`; the two
    /// arities are disambiguated as `_label_sets` (this one) and `_nodes`.
    ///
    /// Detects whether `sub_concept_set` carries a concept that `super_concept_set`
    /// contains with the opposite negation (a clash → returns true). `sub_set_flag`,
    /// when supplied, reports whether `sub_concept_set` is a subset of
    /// `super_concept_set` (nominal concepts ignored when `ignore_nominals_for_subset_checking`).
    pub fn is_label_concept_clash_set_label_sets(
        &mut self,
        sub_concept_set: LabelSetId,
        super_concept_set: LabelSetId,
        sub_set_flag: Option<&mut bool>,
        ignore_nominals_for_subset_checking: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // STATINC(LABELCONCEPTSUBSETTESTCOUNT, calcAlgContext);
        let sub_con_set_count = calc_alg_context
            .process_context()
            .label_set(sub_concept_set)
            .get_concept_count();
        let super_con_set_count = calc_alg_context
            .process_context()
            .label_set(super_concept_set)
            .get_concept_count();
        let threshold_factor = self.map_comparison_direct_lookup_factor;
        // if (subSetFlag) *subSetFlag = true;
        if let Some(flag) = sub_set_flag {
            *flag = true;
        }
        if sub_con_set_count * threshold_factor < super_con_set_count {
            // W6-DEFER[api]: direct-lookup branch (`CReapplyConceptLabelSetIterator`,
            // unported LS-1 stub). Faithful logic:
            //   subConSetIt = subConceptSet->getConceptLabelSetIterator(true,false,false);
            //   while subConSetIt.hasValue():
            //     subConDes = subConSetIt.getConceptDescriptor();
            //     containedNegation = false;
            //     if superConceptSet->containsConcept(subConDes->getConcept(), &containedNegation):
            //       if containedNegation != subConDes->getNegation(): return true;   // CLASH
            //     else if !ignoreNominalsForSubsetChecking || subConDes->getConcept()->getOperatorCode() != CCNOMINAL:
            //       *subSetFlag = false;
            //     subConSetIt.moveNext();
        } else {
            // W6-DEFER[api]: tag-merge branch over both sorted iterators. Faithful logic:
            //   subConSetIt  = subConceptSet->getConceptLabelSetIterator(true,false,false);
            //   superConSetIt = superConceptSet->getConceptLabelSetIterator(true,false,false);
            //   superConDes = superConSetIt.getConceptDescriptor(); superConTag = superConDes->getConceptTag(); superConSetIt.moveNext();
            //   while subConSetIt.hasValue():
            //     subConDes = subConSetIt.getConceptDescriptor(); subConTag = subConDes->getConceptTag();
            //     conceptInSuperConSet = true;
            //     while superConTag < subConTag:
            //       if !superConSetIt.hasValue(): *subSetFlag = false; return false;
            //       superConDes = superConSetIt.getConceptDescriptor(); superConTag = superConDes->getConceptTag(); superConSetIt.moveNext();
            //     if subConTag != superConTag: conceptInSuperConSet = false;
            //     else if subConDes->isNegated() != superConDes->isNegated(): return true;   // CLASH
            //     if !conceptInSuperConSet && (!ignoreNominalsForSubsetChecking
            //          || subConDes->getConcept()->getOperatorCode() != CCNOMINAL): *subSetFlag = false;
            //     subConSetIt.moveNext();
        }
        let _ = (ignore_nominals_for_subset_checking, calc_alg_context);
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::isLabelConceptClashSet`
    /// (node / node form, building clash descriptors). cpp 20867–20932.
    ///
    /// KONCLUDE-PORT-NOTE[overload]: the `_nodes` arity of the overloaded
    /// `isLabelConceptClashSet` (see `_label_sets`).
    ///
    /// Detects a clashing concept pair between the two individuals' concept label
    /// sets and, on the first clash, prepends both sides' clashed-concept descriptors
    /// onto `clash_descriptors`. The smaller set is taken as `sub` (the lookup side);
    /// the per-concept iterator walks are deferred (LS-1 stub).
    pub fn is_label_concept_clash_set_nodes(
        &mut self,
        sub_set_indi: NodeId,
        super_set_indi: NodeId,
        clash_descriptors: &mut ClashDescId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // STATINC(INDINODESMERGEABLECONCEPTSETTESTCOUNT, calcAlgContext);
        // KONCLUDE-PORT-NOTE[ownership]: the C++ value params `subSetIndi`/`superSetIndi`
        // are reassigned by the count-swap and then passed by `CIndividualProcessNode*&`
        // to `createClashedConceptDescriptor`; modelled as local `mut` bindings + `&mut`.
        let mut sub_set_indi = sub_set_indi;
        let mut super_set_indi = super_set_indi;

        let mut sub_concept_set = calc_alg_context
            .process_context_mut()
            .node_mut(sub_set_indi)
            .get_reapply_concept_label_set(false);
        let mut super_concept_set = calc_alg_context
            .process_context_mut()
            .node_mut(super_set_indi)
            .get_reapply_concept_label_set(false);

        // if (superConceptSet->getConceptCount() < subConceptSet->getConceptCount()) { swap sets + indis }
        let super_count = calc_alg_context
            .process_context()
            .label_set(super_concept_set)
            .get_concept_count();
        let sub_count = calc_alg_context
            .process_context()
            .label_set(sub_concept_set)
            .get_concept_count();
        if super_count < sub_count {
            std::mem::swap(&mut sub_concept_set, &mut super_concept_set);
            std::mem::swap(&mut sub_set_indi, &mut super_set_indi);
        }

        let sub_con_set_count = calc_alg_context
            .process_context()
            .label_set(sub_concept_set)
            .get_concept_count();
        let super_con_set_count = calc_alg_context
            .process_context()
            .label_set(super_concept_set)
            .get_concept_count();
        let threshold_factor = self.map_comparison_direct_lookup_factor;
        if sub_con_set_count * threshold_factor < super_con_set_count {
            // W6-DEFER[api]: direct-lookup branch (`CReapplyConceptLabelSetIterator` +
            // `getConceptDescriptor(concept, out conDes, out depTrackPoint)`, unported
            // LS-1 stub). Faithful logic:
            //   subConSetIt = subConceptSet->getConceptLabelSetIterator(true,false,false);
            //   while subConSetIt.hasValue():
            //     subConDes = subConSetIt.getConceptDescriptor(); subDepTrackPoint = subConSetIt.getDependencyTrackPoint();
            //     if superConceptSet->getConceptDescriptor(subConDes->getConcept(), superConDes, superDepTrackPoint):
            //       if superConDes->getNegation() != subConDes->getNegation():
            //         clashDescriptors = createClashedConceptDescriptor(clashDescriptors, &subSetIndi, subConDes, subDepTrackPoint, ctx);
            //         clashDescriptors = createClashedConceptDescriptor(clashDescriptors, &superSetIndi, superConDes, superDepTrackPoint, ctx);
            //     subConSetIt.moveNext();
        } else {
            // W6-DEFER[api]: tag-merge branch over both sorted iterators. Faithful logic:
            //   conSet1It = subConceptSet->getConceptLabelSetIterator(true,false,false);
            //   conSet2It = superConceptSet->getConceptLabelSetIterator(true,false,false);
            //   conDes2 = conSet2It.getConceptDescriptor(); depTrackPoint2 = conSet2It.getDependencyTrackPoint();
            //   conTag2 = conDes2->getConceptTag(); conSet2It.moveNext();
            //   while conSet1It.hasValue():
            //     conDes1 = conSet1It.getConceptDescriptor(); depTrackPoint1 = conSet1It.getDependencyTrackPoint(); conTag1 = conDes1->getConceptTag();
            //     while conTag2 < conTag1:
            //       if !conSet2It.hasValue(): return false;
            //       conDes2 = conSet2It.getConceptDescriptor(); depTrackPoint2 = conSet2It.getDependencyTrackPoint(); conTag2 = conDes2->getConceptTag(); conSet2It.moveNext();
            //     if conTag1 == conTag2 && conDes1->isNegated() != conDes2->isNegated():
            //       clashDescriptors = createClashedConceptDescriptor(clashDescriptors, &subSetIndi, conDes1, depTrackPoint1, ctx);
            //       clashDescriptors = createClashedConceptDescriptor(clashDescriptors, &superSetIndi, conDes2, depTrackPoint2, ctx);
            //       return true;   // CLASH (early)
            //     conSet1It.moveNext();
            // (`createClashedConceptDescriptor` is this unit; live once LS-1 iterator lands.)
        }
        let _ = (clash_descriptors, sub_set_indi, super_set_indi, calc_alg_context);
        false
    }
}
