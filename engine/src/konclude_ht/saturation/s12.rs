//! `saturation::s12` — Statistics + debug string generation (port unit #12 of 12,
//! the LAST). Faithful port of group O of Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauApproximationSaturationTaskHandleAlgorithm.cpp`
//! (manifest `03-saturation-calc.md`, PU-SAT-DBG "Statistics + debug string
//! generation"; the cpp tail). Methods ported here, with cpp line ranges:
//!
//!   * `writeIndividualSaturationStatistics`        (cpp 532–587),
//!   * `testInsufficientIndividuls`                 (cpp 591–611),
//!   * `testRelevantConceptRoleRatio`               (cpp 632–686),
//!   * `writeGeneratedExtendedDebugIndiModelStringList` (cpp 8025–8051),
//!   * `generateExtendedDebugIndiModelStringList`   (cpp 8054–8331),
//!   * `generateStatusFlagsStringList`              (cpp 8333–8378),
//!   * `getDebugIndividualConceptName`              (cpp 8380–8392),
//!   * `generateDebugIndiModelStringList`           (cpp 8394–8434),
//!   * `testDebugSaturationTaskContainsConcepts`    (cpp 8439–8453),
//!   * `testDebugSaturationTaskContainsConcept`     (cpp 8456–8478).
//!
//! NOT re-ported here (already in `saturation/algorithm.rs` as field getters,
//! lines 280–293): the seven `getApplied{AND,OR,SOME,ATLEAST,ALL,ATMOST,Total}RuleCount`
//! accessors (cpp 7993–8019). Re-emitting them would duplicate the `impl`.
//! `tryAssociateIndividualNodesWithBackendCache` (cpp 615) is the cache hand-off
//! (group N) and belongs to PU-SAT-11, not this unit.
//!
//! KONCLUDE-PORT-NOTE[ownership]: each method is a member of
//! `CCalculationTableauApproximationSaturationTaskHandleAlgorithm`, so it becomes
//! `&mut self`. Per the port-wide context convention the C++
//! `CCalculationAlgorithmContextBase*` is threaded explicitly as a trailing
//! `calc_alg_context: &mut CalculationAlgorithmContextBase`. `CIndividualSaturationProcessNode*`
//! arguments become `SatNodeId` (arena id into the per-test `sat_nodes` pool);
//! `CConcept*` → `ConceptId`; `QString`/`QStringList` → `String`/`Vec<String>`;
//! `QStringList* list` (out-param) → `Option<&mut Vec<String>>`.
//!
//! KONCLUDE-PORT-NOTE[api]: this is the **statistics / debug** group, classified
//! "optional/drop" by the manifest — it has NO calculus effect (it builds debug
//! strings, writes `QFile`s, and sets local `bug` booleans). Its bodies bottom
//! out almost entirely in not-yet-ported subsystems, so the control flow is
//! transcribed and the unported leaves deferred (no calculus logic is dropped):
//!   - the per-test saturation satellites `W4-DEFER[api]`:
//!     `CIndividualSaturationProcessNodeVector` (the `getIndividualSaturationProcessNodeVector`
//!     databox getter + `getItemCount`/`getData`), `CReapplyConceptSaturationLabelSet`
//!     (+ its iterator) and `CConceptSaturationDescriptor` chains,
//!     `CRoleBackwardSaturationPropagationHash` / `CBackwardSaturationPropagationLink`,
//!     `CLinkedRoleSaturationSuccessorHash` / `CSaturationSuccessorData`,
//!     `CExtendedConceptReferenceLinkingData` / `CSaturationConceptDataItem`,
//!     `CIndividualSaturationProcessNodeStatusFlags` `has*Flag` predicates
//!     (the flag masks are still pending — `flags` is a bare `Cint64`),
//!     `CCriticalIndividualNodeConceptTestSet`, the per-node
//!     `getAppliedDatatypeData` datatype satellite;
//!   - the text formatters `CConceptTextFormater` / `CIRIName` and the
//!     `CConcept`/`CRole` name+tag readers (datatype/property-name/IRI lookups);
//!   - the `Qt` file/string I/O (`QFile`, `QIODevice`, `QChar`);
//!   - the cache/task handles `W6-DEFER[api]`: `mBackendAssCaceHandler`, the
//!     `CSatisfiableCalculationTask` debug-testing task + its `CProcessingDataBox`
//!     completion-node vector / `CReapplyConceptLabelSet::containsConcept`.
//! The real, portable leaves ARE emitted: the `self.debug_indi_model_string*`
//! field reads/writes, the `mDebugTestingSaturationTask` null-guard, the
//! `firstIndiID/lastIndiID` clamping arithmetic, and the sibling `self.*` calls
//! (`generate_extended_debug_indi_model_string_list`,
//! `generate_status_flags_string_list`, `test_debug_saturation_task_contains_concept`).

#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_mut)]

use super::super::completion::context::CalculationAlgorithmContextBase;
use super::super::model::substrate::{Cint64, Id};
use super::super::model::ConceptId;
use super::super::process::sat_node::IndividualSaturationProcessNodeStatusFlags;
use super::super::process::SatNodeId;

impl super::algorithm::SaturationTaskHandleAlgorithm {
    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::writeIndividualSaturationStatistics`
    /// (cpp 532–587). Debug-only: writes per-individual saturation statistics to
    /// `./Debugging/SaturationTasks/saturation-statistics.txt`.
    pub fn write_individual_saturation_statistics(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W4-DEFER[api]: the entire body iterates the per-test saturation
        //   satellites and writes a Qt file:
        //   CIndividualSaturationProcessNodeVector* indiVec =
        //       calcAlgContext->getProcessingDataBox()->getIndividualSaturationProcessNodeVector(false);
        //   QFile tmpFile("./Debugging/SaturationTasks/saturation-statistics.txt");
        //   if (tmpFile.open(...)) {
        //     write header;
        //     for each indi in indiVec:
        //       indiName = getDebugIndividualConceptName(indi, calcAlgContext)        [self.* sibling, here]
        //       indiDirectFlags  = generateStatusFlagsStringList(indi->getDirectStatusFlags(), ...).join(",")
        //       indiIndirectFlags= generateStatusFlagsStringList(indi->getIndirectStatusFlags(), ...).join(",")
        //       conCount/totalCount/implCount  <- indi->getReapplyConceptSaturationLabelSet(false)
        //       roleBack{,Prop,Link}Count      <- indi->getRoleBackwardPropagationHash(false) iteration
        //                                         (CBackwardSaturationPropagationLink / ...ReapplyDescriptor)
        //       write tab-separated row;
        //   }
        //   The `getIndividualSaturationProcessNodeVector` databox getter, the
        //   label-set / role-backward-propagation-hash satellites, the
        //   `has*Flag` status-flag predicates, and the QFile sink are all unported;
        //   the `cint64 insufficientCount = 0;` C++ local is dead (never read).
        //   No calculus state is touched. Deferred as a whole.
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::testInsufficientIndividuls`
    /// (cpp 591–611). Debug-only: counts nominal nodes flagged insufficient and
    /// sets a (no-op) `bool bug` breakpoint local when any exist.
    pub fn test_insufficient_individuls(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let mut insufficient_count: Cint64 = 0;
        // W4-DEFER[api]: the iteration over
        //   calcAlgContext->getProcessingDataBox()->getIndividualSaturationProcessNodeVector(false)
        //   resolves the (unported) sat-node vector getter; per node:
        //     if (indi->getNominalIndividual())
        //       if (indi->getIndirectStatusFlags()->hasInsufficientFlag())
        //         ++insufficientCount;
        //   `getNominalIndividual()` reads the node's nominal id (ported field
        //   `nominal_indi`) but the vector getter and the `hasInsufficientFlag`
        //   status-flag predicate are pending, so the count stays 0.
        if insufficient_count > 0 {
            // C++: `bool bug = true;` — a debugger breakpoint sentinel; no effect.
            let _bug = true;
        }
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::testRelevantConceptRoleRatio`
    /// (cpp 632–686). Debug-only: tallies relevant-vs-total concept and role
    /// counts across saturation nodes. The four totals are local and never read
    /// (pure measurement spot), so the body has no calculus effect.
    pub fn test_relevant_concept_role_ratio(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let mut total_concept_count: Cint64 = 0;
        let mut relevant_concept_count: Cint64 = 0;
        let mut total_role_count: Cint64 = 0;
        let mut relevant_role_count: Cint64 = 0;
        // W4-DEFER[api]: iterates getIndividualSaturationProcessNodeVector(false);
        //   per node walks indi->getReapplyConceptSaturationLabelSet(false) concept
        //   descriptors (relevant <- ((CConceptProcessData*)concept->getConceptData())
        //   ->hasInferRelevantFlag()) and indi->getRoleBackwardPropagationHash(false)
        //   role-backward links (relevant <- ((CRoleProcessData*)role->getRoleData())
        //   ->hasInferRelevantFlag()), incrementing the four counters. The
        //   sat-vector getter, the label-set / role-backward-prop-hash satellites,
        //   and the CConceptProcessData / CRoleProcessData infer-relevant flags are
        //   pending; the counters stay 0 and are never read.
        let _ = (
            &mut total_concept_count,
            &mut relevant_concept_count,
            &mut total_role_count,
            &mut relevant_role_count,
        );
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::writeGeneratedExtendedDebugIndiModelStringList`
    /// (cpp 8025–8051). Generates the extended debug model string list, writes the
    /// per-node strings (plus the remaining-debug tail) to `filename`, and caches
    /// the joined model string on `self`. Returns the cached model string.
    pub fn write_generated_extended_debug_indi_model_string_list(
        &mut self,
        filename: &str,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
        first_indi_id: Cint64,
        last_indi_id: Cint64,
    ) -> String {
        let mut indi_string_list: Vec<String> = Vec::new();
        let remaining_debug_string = self.generate_extended_debug_indi_model_string_list(
            calc_alg_context,
            first_indi_id,
            last_indi_id,
            Some(&mut indi_string_list),
        );

        // W6-DEFER[api]: the QFile sink —
        //   QFile file(filename);
        //   if (file.open(QIODevice::WriteOnly)) {
        //     for (const QString& tmpString : indiStringList) {
        //       write tmpString.replace("<br>","").replace("<p>","\n"); write "\r\n\r\n\r\n";
        //     }
        //     write remainingDebugString; file.close();
        //   }
        let _ = filename;

        if indi_string_list.len() < 100000 {
            self.debug_indi_model_string_list = indi_string_list;
            self.debug_indi_model_string = self.debug_indi_model_string_list.join("<br><p><br>\r\n");
            self.debug_indi_model_string += remaining_debug_string.as_str();
        }

        self.debug_indi_model_string.clone()
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::generateExtendedDebugIndiModelStringList`
    /// (cpp 8054–8331). Builds, per saturation node, a verbose HTML-ish debug
    /// string (label set, applied data literal, backward links, successor links,
    /// forwarding/dependency nodes, direct/indirect status flags, clashed
    /// concepts), then either caches the joined string on `self` or returns it via
    /// the `list` out-param.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: the C++ default args
    /// (`firstIndiID=0, lastIndiID=-1, list=nullptr`) are passed explicitly by
    /// callers; `QStringList* list` → `Option<&mut Vec<String>>`.
    pub fn generate_extended_debug_indi_model_string_list(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
        first_indi_id: Cint64,
        last_indi_id: Cint64,
        list: Option<&mut Vec<String>>,
    ) -> String {
        // W4-DEFER[api]: the node vector —
        //   CProcessingDataBox* procDataBox = calcAlgContext->getUsedProcessingDataBox();
        //   CIndividualSaturationProcessNodeVector* indiVec =
        //       procDataBox->getIndividualSaturationProcessNodeVector();
        //   cint64 indiCount = indiVec->getItemCount();
        //   The `getIndividualSaturationProcessNodeVector` getter is pending, so the
        //   item count is taken as 0 and the per-node loop below runs empty.
        let mut indi_count: Cint64 = 0; // indiVec->getItemCount()  (W4-DEFER[api])
        let mut first_indi_id = first_indi_id;
        if last_indi_id >= 0 {
            indi_count = last_indi_id.min(indi_count);
        }
        first_indi_id = first_indi_id.min(indi_count);

        let mut indi_string_list: Vec<String> = Vec::new();
        let mut i = first_indi_id;
        while i < indi_count {
            // W4-DEFER[api]: the per-node debug string assembly (cpp 8064–8298).
            //   indi = indiVec->getData(i); if (indi) { ... }
            //   For each node the C++ builds, in order:
            //     - nominalString: from indi->getSaturationConceptReferenceLinking()
            //         (CSaturationConceptDataItem -> getSaturationConcept()/getSaturationNegation(),
            //          class name via CIRIName / concept tag with ¬ prefix) else the
            //          nominal individual name, else ",Resolved-Extension-Node";
            //     - refModeString: indi->getReferenceIndividualSaturationProcessNode()
            //         + getReferenceMode() (1=substitute, 2=copy) [ported fields
            //         reference_indi_node / reference_mode];
            //     - conSetString: walk indi->getReapplyConceptSaturationLabelSet(false)
            //         CConceptSaturationDescriptor chain (skip conTag==1),
            //         CConceptTextFormater::getConceptString + "{critical checked}" when
            //         getSaturationCriticalIndividualNodeConceptTestSet(false)
            //         ->isConceptTestedForIndividual(conDes, indi);
            //     - appliedDataLiteralString: indi->getAppliedDatatypeData(false) literal/datatype;
            //     - propString: indi->getRoleBackwardPropagationHash(false) role+source-node list;
            //     - succString: indi->getLinkedRoleSuccessorHash(false) per-role successor
            //         data (~extension/~base, ~active/~inactive, ~all-ext-queued, creation roles);
            //     - depIndiString: indi->getCopyDependingIndividualNodeLinker() forwarding list
            //         [ported field depending_indi_node_linker];
            //     - directFlagString: generateStatusFlagsStringList(indi->getDirectStatusFlags(), ...)
            //         + "individual representation node"/"occurrence statistics ..." markers
            //         [ported flags abox_individual_representation_node /
            //          occurrence_statistics_collecting_required / occurrence_statistics_collected];
            //     - indirectFlagString: generateStatusFlagsStringList(indi->getIndirectStatusFlags(), ...);
            //     - clashedString: indi->getClashedConceptSaturationDescriptorLinker() chain.
            //   It then pushes the assembled `indiString` to `indiStringList`.
            //   All of these read unported saturation satellites / text formatters,
            //   so the assembly is deferred; the loop is empty (indi_count == 0).
            i += 1;
        }

        // The list-handling tail (cpp 8303–8330) IS portable — real `self` mutations:
        match list {
            None => {
                if indi_string_list.len() >= 1000000 {
                    // W6-DEFER[api]: the overflow QFile dump —
                    //   QFile file("./Debugging/SaturationTasks/tmp-<taskDepth>.txt");
                    //   if (file.open(...)) { write each tmpString.replace("<br>","\r\n") + "\r\n\r\n\r\n"; }
                    //   (calcAlgContext->getUsedSatisfiableCalculationTask()->getTaskDepth())
                } else {
                    self.debug_indi_model_string_list = indi_string_list;
                    self.debug_indi_model_string =
                        self.debug_indi_model_string_list.join("<br>\n<p><br>\n\r\n");
                }
            }
            Some(out_list) => {
                self.debug_indi_model_string.clear();
                *out_list = indi_string_list;
            }
        }

        self.debug_indi_model_string.clone()
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::generateStatusFlagsStringList`
    /// (cpp 8333–8378). Maps a status-flag word to a human-readable label list
    /// (falling back to `["none"]` when no flag is set).
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: C++ `CIndividualSaturationProcessNodeStatusFlags*`
    /// → the inline `Copy` value `IndividualSaturationProcessNodeStatusFlags`.
    pub fn generate_status_flags_string_list(
        &mut self,
        status_flags: IndividualSaturationProcessNodeStatusFlags,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> Vec<String> {
        let mut flags_string_list: Vec<String> = Vec::new();
        // W4-DEFER[api]: the `has*Flag` predicates on
        //   CIndividualSaturationProcessNodeStatusFlags are not yet ported — the
        //   flag masks land with the saturation status-flag unit and `flags` is a
        //   bare `Cint64`. The faithful predicate ladder is transcribed below with
        //   each test deferred to `false`, so the structure (and the "none"
        //   fallback) is preserved; when the masks land, swap each `false` for the
        //   real `status_flags.has_*_flag()`.
        let _ = status_flags;
        if false /* status_flags.has_clashed_flag() */ {
            flags_string_list.push("clashed".to_string());
        }
        if false /* status_flags.has_insufficient_flag() */ {
            flags_string_list.push("insufficient".to_string());
        }
        if false /* status_flags.has_nominal_connection_flag() */ {
            flags_string_list.push("nominal connection".to_string());
        }
        if false /* status_flags.has_critical_flag() */ {
            flags_string_list.push("critical".to_string());
        }
        if false /* status_flags.has_cardinality_proplematic_flag() */ {
            flags_string_list.push("cardinality problematic".to_string());
        }
        if false /* status_flags.has_eq_candidate_proplematic_flag() */ {
            flags_string_list.push("eqCandidate problematic".to_string());
        }
        if false /* status_flags.has_missed_abox_consistency_flag() */ {
            flags_string_list.push("missed ABox consistency data".to_string());
        }
        if false /* status_flags.has_initialized_flag() */ {
            flags_string_list.push("initialized".to_string());
        }
        if false /* status_flags.has_completed_flag() */ {
            flags_string_list.push("completed".to_string());
        }
        if false /* status_flags.has_unprocessed_flag() */ {
            flags_string_list.push("unprocessed".to_string());
        }
        if false /* status_flags.has_unmarked_role_assertion_flag() */ {
            flags_string_list.push("unmarked role assertion".to_string());
        }
        if false /* status_flags.has_unregistered_propagation_flag() */ {
            flags_string_list.push("unregistered role assertion".to_string());
        }
        if false /* status_flags.has_propagation_incomplete_flag() */ {
            flags_string_list.push("propagation incomplete".to_string());
        }
        if flags_string_list.is_empty() {
            flags_string_list.push("none".to_string());
        }
        flags_string_list
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::getDebugIndividualConceptName`
    /// (cpp 8380–8392). Returns the class-name IRI of the node's initialising
    /// saturation concept (empty when none / negated / not class-named).
    pub fn get_debug_individual_concept_name(
        &mut self,
        indi: SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> String {
        // W4-DEFER[api]:
        //   CExtendedConceptReferenceLinkingData* extConRefLinkData =
        //       indi->getSaturationConceptReferenceLinking();
        //   CSaturationConceptDataItem* conceptSatItem = (CSaturationConceptDataItem*)extConRefLinkData;
        //   if (conceptSatItem) {
        //     CConcept* initializedConcept = conceptSatItem->getSaturationConcept();
        //     bool initializedNegation = conceptSatItem->getSaturationNegation();
        //     if (initializedConcept->hasClassName() && !initializedNegation)
        //       nominalString = CIRIName::getRecentIRIName(initializedConcept->getClassNameLinker());
        //   }
        //   The CExtendedConceptReferenceLinkingData / CSaturationConceptDataItem
        //   satellite, the concept class-name reader, and CIRIName are unported;
        //   the result is the empty string.
        let _ = indi;
        String::new()
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::generateDebugIndiModelStringList`
    /// (cpp 8394–8434). Builds the compact `[ id ] = { concepts }` debug model
    /// string list and caches the newline-joined string on `self`.
    pub fn generate_debug_indi_model_string_list(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> String {
        // W4-DEFER[api]: the node vector + per-node label-set walk —
        //   CProcessingDataBox* procDataBox = calcAlgContext->getUsedProcessingDataBox();
        //   CIndividualSaturationProcessNodeVector* indiVec =
        //       procDataBox->getIndividualSaturationProcessNodeVector();
        //   for each indi: conSet = indi->getReapplyConceptSaturationLabelSet(false);
        //     if (conSet) { iterate conSet (CReapplyConceptSaturationLabelSetIterator),
        //        skip conTag==1, build "<neg?>-<tag><className?>" comma list,
        //        push "[ <id> ] = { <conSet> } "; }
        //   The sat-vector getter, the label set + its iterator, and the concept
        //   class-name reader are pending, so the list is empty.
        let indi_string_list: Vec<String> = Vec::new();

        // Real `self` mutations (cpp 8431–8433):
        self.debug_indi_model_string_list = indi_string_list;
        self.debug_indi_model_string = self.debug_indi_model_string_list.join("\n");
        self.debug_indi_model_string.clone()
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::testDebugSaturationTaskContainsConcepts`
    /// (cpp 8439–8453). For each concept in the node's saturation label set, calls
    /// the single-concept containment check.
    pub fn test_debug_saturation_task_contains_concepts(
        &mut self,
        indi_node: SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W4-DEFER[api]: the label-set iteration —
        //   CReapplyConceptSaturationLabelSet* conSet = indiNode->getReapplyConceptSaturationLabelSet();
        //   if (conSet) {
        //     CReapplyConceptSaturationLabelSetIterator it = conSet->getIterator(true,false);
        //     while (it.hasNext()) {
        //       conSatDes = it.getConceptSaturationDescriptor();
        //       if (conSatDes) testDebugSaturationTaskContainsConcept(
        //           conSatDes->getConcept(), conSatDes->getNegation(), indiNode, calcAlgContext);  [self.*]
        //       it.moveNext();
        //     }
        //   }
        //   The CReapplyConceptSaturationLabelSet + iterator + CConceptSaturationDescriptor
        //   are unported, so no per-concept check is dispatched; the sibling leaf
        //   `self.test_debug_saturation_task_contains_concept(...)` is ready for the
        //   reconcile pass.
        let _ = indi_node;
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::testDebugSaturationTaskContainsConcept`
    /// (cpp 8456–8478). When a debug-testing completion task is installed, checks
    /// that the matching completion node's label contains `concept`; on a miss it
    /// regenerates + dumps the extended debug model (a debugger breakpoint helper).
    pub fn test_debug_saturation_task_contains_concept(
        &mut self,
        concept: ConceptId,
        con_negation: bool,
        indi_node: SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // The `mDebugTestingSaturationTask` null-guard IS portable.
        if self.debug_testing_saturation_task != Id::NONE {
            // W6-DEFER[api]: the completion-task containment check —
            //   cint64 individualID = indiNode->getIndividualID();
            //   CProcessingDataBox* procDataBox = mDebugTestingSaturationTask->getProcessingDataBox();
            //   if (procDataBox) {
            //     CIndividualProcessNode* indiNode = procDataBox->getIndividualProcessNodeVector()->getData(individualID);
            //     bool contained = indiNode->getReapplyConceptLabelSet(false)->containsConcept(concept, conNegation);
            //     if (!contained) {
            //       mDebugTestSaturationDebugIndiModelString = generateExtendedDebugIndiModelStringList(calcAlgContext);  [self.*]
            //       QFile tmpFile("tmp4.txt"); write mDebugTestSaturationDebugIndiModelString;
            //       bool bug = true;  // breakpoint sentinel, no effect
            //     }
            //   }
            //   The debug-testing CSatisfiableCalculationTask, its CProcessingDataBox
            //   completion-node vector, and CReapplyConceptLabelSet::containsConcept are
            //   unported; the `generate_extended_debug_indi_model_string_list(self, ctx, 0, -1, None)`
            //   regeneration + QFile dump land on reconcile. No calculus effect.
            let _ = (concept, con_negation, indi_node);
        }
    }
}
