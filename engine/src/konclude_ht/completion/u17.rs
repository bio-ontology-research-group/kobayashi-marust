//! `completion::u17` — Nominal / value-space / backend-cache-synchronisation
//! family, batch (port unit #17 of 36).
//!
//! Faithful port of the 13 methods that the manifest (`01-completion-methods.md`,
//! "Unit 17") groups under nominal handling but which are, in fact, the
//! value-space (datatype) trigger helpers, the data-assertion successor builder,
//! the saturation-cache expansion shortcuts, and the representative-backend-cache
//! synchronisation accessors of Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.cpp`.
//! cpp source line ranges (1-based) per method are noted on each item.
//!
//! Methods (cpp order):
//!   * `checkValueSpaceDistinctSatisfiability`        [9172–9212]
//!   * `triggerValueSpaceConcepts`                    [9215–9231]
//!   * `addtriggeredValueSpaceConcepts`               [9236–9254]
//!   * `createDATAASSERTIONDependency`                [10033–10039]
//!   * `getRepresentativeJoiningKeyData`              [10771–10799]
//!   * `addDataAssertion`                             [14457–14492]
//!   * `tryInitalizingFromSaturatedData`              [21737–21852]
//!   * `tryExpansionFromSaturatedData`                [22081–22140]
//!   * `loadIndividualNodeDataFromBackendCache`       [22618–22696]
//!   * `visitIndividualsRelevantBackendSynchronisationDataIndividuals` [22988–23025]
//!   * `getBackendSynchronizationFilledRoleNeighbourExpansionDataHash` [23738–23772]
//!   * `getLocalizedIndividualBackendCacheSnychronisationData`         [23984–23993]
//!   * `testIndividualNodeBackendCacheNominalIndirectConnectionBlockingCritical` [25891–26001]
//!
//! KONCLUDE-PORT-NOTE[ownership]: each method is a member of
//! `CCalculationTableauCompletionTaskHandleAlgorithm`, so it becomes `&mut self`
//! plus the threaded per-thread context `calc_alg_context: &mut
//! CalculationAlgorithmContextBase`. C++ `CIndividualProcessNode*&` /
//! `CConceptDescriptor**` out/in-out pointer-references become `&mut NodeId` /
//! `&mut ConDescId` (arena ids); a plain `CXxx*` value parameter becomes the
//! matching `*Id`. The per-test arenas are reached through the context as
//! `calc_alg_context.process_context()` / `_mut()` (the Base forwarder for the
//! by-value `used_process_context`), the databox as
//! `calc_alg_context.processing_data_box{,_mut}()`, and the static terminology as
//! `calc_alg_context.ontology_arenas()`.
//!
//! Deferral landscape. This unit sits almost entirely on top of FOUR subsystems
//! that are not yet ported, so most bodies cannot resolve their typed locals:
//!   1. the **datatype handler** (`mDatatypeHandler`,
//!      `CDatatypeIndividualProcessNodeHandler`) — value-space reasoning;
//!      a zero-size `Id` stub today → `// W6-DEFER[api]`.
//!   2. the **representative-memory backend cache** family
//!      (`CIndividualNodeRepresentativeMemoryBackendCacheSynchronisationData`,
//!      `CBackendRepresentativeMemoryCacheIndividualAssociationData`, the label
//!      cache items, the role-neighbour expansion arrays) — `mBackendCacheHandler`
//!      and the per-node sync data are zero-size `Id`/stub markers today
//!      → `// W6-DEFER[api]`.
//!   3. the **saturation expansion cache** (`mUsedSatNodeExpCacheHandler`,
//!      `CSaturationNodeAssociatedDeterministicConceptExpansion`,
//!      `CReapplyConceptSaturationLabelSet`, the sat reference-linking chain)
//!      → `// W6-DEFER[api]`.
//!   4. the **representative variable-binding-path** propagation hashes
//!      (`CRepresentativeVariableBindingPathSetData`, the joining key maps)
//!      — same not-yet-ported family that gates the u05 representative rules.
//!
//! Following the porting convention: the three genuinely substrate-portable
//! methods are ported in full —
//!   * `addtriggeredValueSpaceConcepts` (a `ConceptDescriptor` chain reversal +
//!      per-descriptor `addConceptToIndividual`),
//!   * `triggerValueSpaceConcepts` (guard + datatype trigger + the above),
//!   * `createDATAASSERTIONDependency` (the `mConfBuildDependencies` guard around
//!      the dependency-factory call), and
//!   * `getLocalizedIndividualBackendCacheSnychronisationData` (the
//!      local-sync-data lazy getter, only the alloc+init deferred).
//! The remaining bodies are driven start-to-finish by the four deferred
//! subsystems and by typed locals of their not-yet-ported classes; they are kept
//! as `// PORT-PENDING` with the faithful signature and a structural
//! transcription of the C++ so a later wave fills them without re-reading the
//! source. Logic is documented, never silently dropped.

#![allow(dead_code)]
#![allow(unused_variables)]

use super::super::model::substrate::{Cint64, Id, INVALID};
use super::super::model::ConceptId;
use super::super::process::representative::{
    RepresentativeVariableBindingPathJoiningKeyHash, RepresentativeVariableBindingPathSetData,
    RepresentativeVariableBindingPathSetDataId, RepresentativeVariableBindingPathSetJoiningHash,
    RepresentativeVariableBindingPathSetJoiningKeyMap,
};
use super::super::process::stubs::{BackendSyncDataId, DataAssertionLinkerId};
use super::super::process::{ConDescId, DependencyId, NodeId, SatNodeId, TrackPointId};
use super::context::CalculationAlgorithmContextBase;

impl super::algorithm::CompletionTaskHandleAlgorithm {
    // =======================================================================
    // Value-space (datatype) trigger helpers (cpp 9172–9254).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::checkValueSpaceDistinctSatisfiability`.
    /// cpp 9172–9212.
    ///
    /// Collects the transitive `differentFrom`-closure of `process_indi` over the
    /// nodes the datatype handler deems relevant, then asks the handler to check
    /// value-space satisfiability of that distinct set.
    pub fn check_value_space_distinct_satisfiability(
        &mut self,
        process_indi: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // C++ guard: `if (mDatatypeHandler && mConfDatatypeReasoning)`.
        if self.datatype_handler != Id::NONE && self.conf_datatype_reasoning {
            // PORT-PENDING: the entire body is datatype-handler driven and uses
            // not-yet-ported facilities:
            //   * two per-test scratch collections — a CPROCESSINGSET and a
            //     CPROCESSINGLIST of CIndividualProcessNode* (pool-allocated);
            //   * `mDatatypeHandler->requiresSatisfiabilityChecking(processIndi, ctx)`;
            //   * a worklist BFS: pop a node, take its `getDistinctHash(false)`,
            //     iterate the distinct ids, `getLocalizedIndividual(id, ctx)` each,
            //     and `mDatatypeHandler->involveDistinctNodeForSatisfiabilityChecking(
            //         nextDistinctIndiNode, ctx)` to decide membership; add unseen
            //     members to both the set and the worklist;
            //   * `mDatatypeHandler->checkSatisfiability(processIndi,
            //         distinctIndividualNodeCollectionSet, ctx)` to finish.
            // W6-DEFER[api]: CDatatypeIndividualProcessNodeHandler is a zero-size
            // stub; the distinct-hash iterator + getLocalizedIndividual sibling +
            // the pooled CPROCESSINGSET/CPROCESSINGLIST are not yet available.
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::triggerValueSpaceConcepts`.
    /// cpp 9215–9231.
    ///
    /// Asks the datatype handler which concepts the node's data literals trigger,
    /// then adds them to the node via `addtriggeredValueSpaceConcepts`.
    pub fn trigger_value_space_concepts(
        &mut self,
        process_indi: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // C++ guard: `if (mDatatypeHandler && mConfDatatypeReasoning)`.
        if self.datatype_handler != Id::NONE && self.conf_datatype_reasoning {
            // `CConceptDescriptor* triggeredConceptLinker = nullptr;`
            let triggered_concept_linker: ConDescId = Id::NONE;

            // W6-DEFER[api]: `mDatatypeHandler->triggerValueSpaceConcepts(processIndi,
            //   triggeredConceptLinker, calcAlgContext)` — the handler fills
            //   `triggeredConceptLinker` (a CConceptDescriptor chain) with the
            //   value-space-triggered concept occurrences. The handler is a
            //   zero-size stub, so the chain stays empty (`Id::NONE`).

            self.addtriggered_value_space_concepts(
                process_indi,
                triggered_concept_linker,
                calc_alg_context,
            );
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addtriggeredValueSpaceConcepts`.
    /// cpp 9236–9254.
    ///
    /// Reverses the triggered-concept descriptor chain (so they are added in the
    /// order the handler produced them) and adds each to the individual.
    pub fn addtriggered_value_space_concepts(
        &mut self,
        process_indi: NodeId,
        triggered_concept_linker: ConDescId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // Reverse the intrusive chain: walk `triggeredConceptLinker`, detach each
        // node (`clearNext`), and prepend it onto `invTriggeredConceptLinker`
        // (`tmp->append(inv)` makes `tmp` the new head with `tmp->next == inv` —
        // the canonical head-front linker convention, see PORT.md §6).
        let mut triggered_concept_linker = triggered_concept_linker;
        let mut inv_triggered_concept_linker: ConDescId = Id::NONE;
        while triggered_concept_linker != Id::NONE {
            let tmp_triggered_concept_linker = triggered_concept_linker;
            triggered_concept_linker = calc_alg_context
                .process_context()
                .con_desc(tmp_triggered_concept_linker)
                .get_next_concept_descriptor();
            // `tmpTriggeredConceptLinker->clearNext()` then
            // `inv = tmpTriggeredConceptLinker->append(inv)`.
            calc_alg_context
                .process_context_mut()
                .con_desc_mut(tmp_triggered_concept_linker)
                .set_next(inv_triggered_concept_linker);
            inv_triggered_concept_linker = tmp_triggered_concept_linker;
        }

        // Add each triggered concept to the node, in reversed (= original) order.
        let mut triggered_concept_linker_it = inv_triggered_concept_linker;
        while triggered_concept_linker_it != Id::NONE {
            let (triggered_concept, triggered_negation, triggered_dependency_track_point, next) = {
                let con_desc = calc_alg_context
                    .process_context()
                    .con_desc(triggered_concept_linker_it);
                (
                    con_desc.get_concept(),
                    con_desc.is_negated(),
                    con_desc.get_dependency_track_point(),
                    con_desc.get_next_concept_descriptor(),
                )
            };
            // W3-DEFER[api]: `addConceptToIndividual(...)` is the sibling core-loop
            // helper (Unit 4, cpp 26692-area family); lands in a later core-loop
            // unit. Faithful call shape preserved.
            let mut process_indi = process_indi;
            self.add_concept_to_individual(
                triggered_concept,
                triggered_negation,
                &mut process_indi,
                triggered_dependency_track_point,
                true,
                false,
                calc_alg_context,
            );
            triggered_concept_linker_it = next;
        }
    }

    // =======================================================================
    // Data-assertion dependency + successor builder (cpp 10033, 14457).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::createDATAASSERTIONDependency`.
    /// cpp 10033–10039.
    ///
    /// Creates a `DATAASSERTION` dependency node (and its continuation track point,
    /// out via `value_dep_track_point`) when dependency tracking is enabled.
    pub fn create_dataassertion_dependency(
        &mut self,
        value_dep_track_point: &mut TrackPointId,
        process_indi: &mut NodeId,
        prev_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> DependencyId {
        let mut dep_node: DependencyId = Id::NONE;
        if self.conf_build_dependencies {
            dep_node = calc_alg_context
                .process_context_mut()
                .create_dataassertion_dependency(
                    value_dep_track_point,
                    process_indi,
                    prev_dep_track_point,
                );
        }
        dep_node
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addDataAssertion`.
    /// cpp 14457–14492.
    ///
    /// Materialises a data-role successor for an ABox data-property assertion:
    /// creates the DATAASSERTION dependency, a fresh successor individual node, the
    /// (reapplied) role link to it, copies the relevant ancestor cache flags, and
    /// (under datatype reasoning) records the data literal + its datatype concept.
    pub fn add_data_assertion(
        &mut self,
        process_indi: &mut NodeId,
        data_assertion_linker: DataAssertionLinkerId,
        dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // PORT-PENDING: faithful transcription of cpp 14457–14492. The body is
        // structurally portable but bottoms out in several not-yet-ported pieces:
        //
        //   role        = dataAssertionLinker->getRole();          // CDataAssertionLinker is a stub
        //   dataLiteral = dataAssertionLinker->getDataLiteral();   //   (no accessors yet)
        //   nextDepTrackPoint = nullptr;
        //   dataAssDepNode = createDATAASSERTIONDependency(nextDepTrackPoint, processIndi,
        //                                                  depTrackPoint, ctx);   // this unit, OK
        //
        //   // generate new data role successor
        //   succIndi = createNewIndividual(nextDepTrackPoint, true, ctx);          // sibling, later unit
        //   ancLink  = createNewIndividualsLinksReapplyed(processIndi, succIndi,
        //                  role->getIndirectSuperRoleList(), role, nextDepTrackPoint, false, ctx); // reapply unit
        //   succIndi->setAncestorLink(ancLink);                                    // ported node setter
        //   succIndi->setIndividualAncestorDepth(processIndi->getIndividualAncestorDepth() + 1); // ported
        //
        //   additionalDataLitLinker = new CProcessAssertedDataLiteralLinker(taskMemMan); // stub linker
        //   additionalDataLitLinker->initProcessDataLiteralLinker(dataLiteral, depTrackPoint);
        //   succIndi->addAssertedDataLiteralLinker(additionalDataLitLinker);
        //   succIndi->setLastAssertedDataLiteralLinker(succIndi->getAssertedDataLiteralLinker());
        //
        //   // ancestor cache-flag inheritance (PORTABLE — uses ported node flag predicates):
        //   if processIndi has (PRFSATISFIABLECACHED | PRFANCESTORSATISFIABLECACHED):
        //       succIndi.add PRFANCESTORSATISFIABLECACHED
        //   if processIndi has (PRFSIGNATUREBLOCKINGCACHED | PRFANCESTORSIGNATUREBLOCKINGCACHED):
        //       succIndi.add PRFANCESTORSIGNATUREBLOCKINGCACHED
        //   if processIndi has (PRFSATURATIONBLOCKINGCACHED | PRFANCESTORSATURATIONBLOCKINGCACHED):
        //       succIndi.add PRFANCESTORSATURATIONBLOCKINGCACHED
        //
        //   // W6-DEFER[api]: datatype handler tail
        //   if (mDatatypeHandler && mConfDatatypeReasoning):
        //       mDatatypeHandler->addDataLiteral(succIndi, dataLiteral, false, nextDepTrackPoint, ctx);
        //       datatype = dataLiteral->getDatatype();
        //       if datatype && datatype->getDatatypeConcept():
        //           addConceptToIndividual(datatype->getDatatypeConcept(), false, succIndi,
        //                                  nextDepTrackPoint, true, false, ctx);
        //
        // Held PORT-PENDING (rather than half-ported) because the successor node
        // identity flows from the unported `createNewIndividual` and every literal
        // operation needs the stubbed CDataAssertionLinker / CDataLiteral /
        // CProcessAssertedDataLiteralLinker accessors.
        let _ = (
            process_indi,
            data_assertion_linker,
            dep_track_point,
            calc_alg_context,
        );
    }

    // =======================================================================
    // Representative variable-binding joining-key data (cpp 10771).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::getRepresentativeJoiningKeyData`.
    /// cpp 10771–10799.
    ///
    /// Lazily builds (and caches) the per-`join_concept` joining-key map over a
    /// representative variable-binding-path set.
    ///
    pub fn get_representative_joining_key_data(
        &mut self,
        rep_var_bind_path_set_data: RepresentativeVariableBindingPathSetDataId,
        join_concept: ConceptId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> RepresentativeVariableBindingPathSetJoiningKeyMap {
        let key_vars = calc_alg_context
            .ontology_arenas()
            .concept(join_concept)
            .get_variable_linker()
            .to_vec();

        let mut joining_data = {
            let ctx = calc_alg_context.process_context_mut();
            let joining_hash = RepresentativeVariableBindingPathSetData::get_joining_hash(
                ctx,
                rep_var_bind_path_set_data,
                false,
            );
            if joining_hash.is_some() {
                RepresentativeVariableBindingPathSetJoiningHash::get_representative_variable_binding_path_set_joining_data(
                    ctx,
                    joining_hash,
                    join_concept,
                    false,
                )
            } else {
                Id::NONE
            }
        };

        if joining_data.is_none() {
            let joining_hash = {
                let ctx = calc_alg_context.process_context_mut();
                RepresentativeVariableBindingPathSetData::get_joining_hash(
                    ctx,
                    rep_var_bind_path_set_data,
                    true,
                )
            };
            joining_data = {
                let ctx = calc_alg_context.process_context_mut();
                RepresentativeVariableBindingPathSetJoiningHash::get_representative_variable_binding_path_set_joining_data(
                    ctx,
                    joining_hash,
                    join_concept,
                    true,
                )
            };

            let var_bind_path_joining_key_hash =
                calc_alg_context.representative_variable_binding_path_joining_key_hash(true);
            let var_bind_paths = {
                let ctx = calc_alg_context.process_context_mut();
                let migrate_data = RepresentativeVariableBindingPathSetData::get_migrate_data(
                    ctx,
                    rep_var_bind_path_set_data,
                    false,
                );
                ctx.rep_var_bind_path_set_migrate_data(migrate_data)
                    .get_representative_variable_binding_path_map()
                    .map
                    .values()
                    .map(|data| data.get_variable_binding_path())
                    .collect::<Vec<_>>()
            };

            for var_bind_path in var_bind_paths {
                let join_key =
                    RepresentativeVariableBindingPathJoiningKeyHash::get_representative_variable_binding_path_joining_key(
                        calc_alg_context.process_context_mut(),
                        var_bind_path_joining_key_hash,
                        var_bind_path,
                        &key_vars,
                        true,
                    );
                let prop_id = calc_alg_context
                    .process_context()
                    .vbpath(var_bind_path)
                    .get_propagation_id();
                let joining_data_map = calc_alg_context
                    .process_context_mut()
                    .rep_var_bind_path_set_joining_data_mut(joining_data)
                    .get_joining_key_map_mut()
                    .get_joining_key_data_map(join_key, true)
                    .expect("created representative joining-key data map");
                joining_data_map.insert(prop_id, var_bind_path);
            }
        }

        calc_alg_context
            .process_context()
            .rep_var_bind_path_set_joining_data(joining_data)
            .get_joining_key_map()
            .clone()
    }

    // =======================================================================
    // Saturation-cache expansion shortcuts (cpp 21737, 22081).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::tryInitalizingFromSaturatedData`.
    /// cpp 21737–21852.
    ///
    /// Fast-path node initialisation from a cached saturation node: if the leading
    /// init concept resolves (via its saturation reference linking) to an
    /// initialised saturation node, replays that node's saturated concept set onto
    /// `indi` (raising a clash exception when the saturation node clashed), records
    /// the saturation blocking data, and adds any remaining init concepts.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: `initConceptLinker`
    /// (`CXSortedNegLinker<CConcept*>*`) is the not-yet-ported sorted-neg concept
    /// chain → opaque `Cint64`.
    pub fn try_initalizing_from_saturated_data(
        &mut self,
        indi: &mut NodeId,
        init_concept_linker: Cint64,
        dep_track_point: TrackPointId,
        allow_preprocess: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // PORT-PENDING: faithful transcription of cpp 21737–21852. Driven entirely
        // by the saturation subsystem (all W6-DEFER[api]):
        //   * resolve `concept = initConceptLinker->getData()` (+ negation), then
        //     its CConceptProcessData -> CConceptReferenceLinking ->
        //     CConceptSaturationReferenceLinkingData ->
        //     CSaturationConceptReferenceLinking ->
        //     getIndividualProcessNodeForConcept() to reach `baseSatIndiNode`;
        //   * follow substitute nodes to the representative `satIndiNode`, take its
        //     CReapplyConceptSaturationLabelSet;
        //   * CLASH: if either sat node has the clashed indirect-status flag, add the
        //     concept (skipping AND processing), build a clashed-concept descriptor,
        //     and `throw CCalculationClashProcessingException(clashDes)`
        //     (KONCLUDE-PORT-NOTE[exceptions]: ported as the clash-propagation
        //     mechanism the engine adopts — Rust has no C++ exceptions);
        //   * else replay: propagate the nominal-connection flag to ancestors
        //     (+ exact-nominal successor-connected-nominal set copy under
        //     `mConfExactNominalDependencyTracking`), add the concept, build the AND
        //     dependency, then for each CConceptSaturationDescriptor in the sat set
        //     `addConceptToIndividualSkipANDProcessing(...)` +
        //     `validateSaturationCachingPossible(...)`; pull any cached
        //     deterministic expansion from
        //     `getUsedSaturationNodeExpansionCacheHandler()` and replay it too
        //     (gated by `mConfSaturationIncompleteExpansionFromCache` /
        //     `requiresNonDeterministicExpansion()`);
        //   * allocate + init a CIndividualNodeSaturationBlockingData from the final
        //     concept count and attach it to `indi`;
        //   * finally add the remaining init concepts (skipping the leading one iff
        //     `baseSatIndiNode == satIndiNode`) via `addConceptToIndividual`.
        //   return true on the fast path; false otherwise.
        let _ = (
            indi,
            init_concept_linker,
            dep_track_point,
            allow_preprocess,
            calc_alg_context,
        );
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::tryExpansionFromSaturatedData`.
    /// cpp 22081–22140.
    ///
    /// The successor-side twin of `try_initalizing_from_saturated_data`: replays a
    /// cached saturation node's concept set onto a freshly created successor
    /// `created_succ_indi` (the SOME/ATLEAST expansion shortcut), with the same
    /// clash / nominal-connection / deterministic-expansion handling.
    pub fn try_expansion_from_saturated_data(
        &mut self,
        indi: &mut NodeId,
        created_succ_indi: NodeId,
        con_des: ConDescId,
        dep_track_point: TrackPointId,
        saturation_indi_node: &mut SatNodeId,
        sat_caching_possible: &mut bool,
        last_sat_cach_possible_con_des: &mut ConDescId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // PORT-PENDING: faithful transcription of cpp 22081–22140. Driven by the
        // saturation subsystem (W6-DEFER[api]):
        //   if saturationIndiNode && saturationIndiNode->isInitialized():
        //     satConSet = saturationIndiNode->getReapplyConceptSaturationLabelSet(false);
        //     if satConSet:
        //       nominalConnectionFlag = saturationIndiNode->getIndirectStatusFlags()->hasNominalConnectionFlag();
        //       if clashed-flag:
        //         if !nominalConnectionFlag || !mOptIncrementalExpansion:
        //           build clashed-concept descriptor from (indi, conDes, depTrackPoint)
        //           and throw CCalculationClashProcessingException   // [exceptions]
        //       else:
        //         if !mOptIncrementalExpansion || !nominalConnectionFlag:
        //           if nominalConnectionFlag:
        //             propagateIndividualNodeNominalConnectionToAncestors(createdSuccIndi, ctx);
        //             if mConfExactNominalDependencyTracking: copy successor-connected-nominal set
        //             propagateIndividualNodeNominalConnectionStatusToAncestors(indi, createdSuccIndi, ctx);
        //           for each CConceptSaturationDescriptor in satConSet:
        //             addConceptToIndividualSkipANDProcessing(satConcept, satConceptNegation,
        //                 createdSuccIndi, depTrackPoint, true, false, true, ctx);
        //             validateSaturationCachingPossible(createdSuccIndi, saturationIndiNode,
        //                 satCachingPossible, lastSatCachPossibleConDes, satConcept, satConceptNegation, ctx);
        //           replay cached deterministic expansion from
        //             getUsedSaturationNodeExpansionCacheHandler() (same gating as above);
        //           return true;
        //   return false;
        let _ = (
            indi,
            created_succ_indi,
            con_des,
            dep_track_point,
            saturation_indi_node,
            sat_caching_possible,
            last_sat_cach_possible_con_des,
            calc_alg_context,
        );
        false
    }

    // =======================================================================
    // Representative-backend-cache synchronisation (cpp 22618–26001).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::loadIndividualNodeDataFromBackendCache`.
    /// cpp 22618–22696.
    ///
    /// On first touch of a nominal node, attaches its representative-backend-cache
    /// synchronisation data (looked up by individual id), tracking same-individual
    /// mergings and scheduled-computation coordination.
    pub fn load_individual_node_data_from_backend_cache(
        &mut self,
        indi_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // PORT-PENDING: faithful transcription of cpp 22618–22696.
        //
        // C++ outer guard:
        //   individual = indiNode->getNominalIndividual();   // W3-DEFER[api]: not yet
        //       // ported on CIndividualProcessNode (only the saturation node has it)
        //   if (mConfIndividualsBackendCacheLoading && mBackendCacheHandler && individual):
        //     if !indiNode->getIndividualBackendCacheSynchronisationData(false):  // ported (pn4)
        //       scheduled = false;
        //       repBackUpdAdapter = getSatisfiableCalculationTask()
        //                             ->getSatisfiableRepresentativeBackendCacheUpdatingAdapter();
        //       if repBackUpdAdapter:
        //         indiCompCoordHash = repBackUpdAdapter->getIndividualComputationCoordinationHash();
        //         coordData = indiCompCoordHash->value(individual->getIndividualID());
        //         if coordData && !coordData->isComputationIntegrated():
        //             coordData->setComputationIntegrated(true); scheduled = true;
        //       indiAssData = mBackendCacheHandler->getIndividualAssociationData(individual, ctx);
        //       if indiAssData:
        //         push indiNode onto databox->LastBackendCacheIntegratedIndividualNodeLinker;
        //         if indiAssData->hasRepresentativeSameIndividualMerging():
        //             databox->incBackendCacheIntegratedSameIndividualNodeCount();
        //         backendSyncData = new CIndividualNodeRepresentativeMemoryBackendCacheSynchronisationData(...);
        //         backendSyncData->initSynchronisationData(indiAssData);
        //         backendSyncData->setBackendCacheSynchron(true);
        //         indiNode->setIndividualBackendCacheSynchronisationData(backendSyncData);
        //         backendSyncData->setScheduledIndividual(scheduled);
        //         return true;
        //       else: same but initSynchronisationData(nullptr) + setBackendCacheSynchron(false);
        //             return true;
        //     else: return true;
        //   return false;
        //
        // Held PORT-PENDING: the `getNominalIndividual()` accessor is not yet ported
        // on `IndividualProcessNode` (W3-DEFER[api]), and the satisfiable-task
        // backend-updating adapter + the
        // CBackendRepresentativeMemoryCacheIndividualAssociationData lookup + the
        // CIndividualNodeRepresentativeMemoryBackendCacheSynchronisationData
        // allocation/init are not yet ported (W6-DEFER[api]). The
        // `mConfIndividualsBackendCacheLoading` / `mBackendCacheHandler` guard
        // fields ARE available (`self.conf_individuals_backend_cache_loading`,
        // `self.backend_cache_handler`) and become live on the reconcile pass.
        let _ = (indi_node, calc_alg_context);
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::visitIndividualsRelevantBackendSynchronisationDataIndividuals`.
    /// cpp 22988–23025.
    ///
    /// Invokes `visit_func` on `indi_node` itself (if it carries backend sync data)
    /// and on every merged individual not already represented in the deterministic
    /// same-individual-set label, optionally localising the merged node first.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: the C++ `std::function<bool(...)>` visitor
    /// becomes a `&mut dyn FnMut`; the merged-node arguments are `NodeId`s.
    pub fn visit_individuals_relevant_backend_synchronisation_data_individuals(
        &mut self,
        indi_node: NodeId,
        localize: bool,
        visit_func: &mut dyn FnMut(NodeId, NodeId, TrackPointId) -> bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // Faithful transcription of cpp 22988–23025. The process-side backend-sync
        // data and its merged-node linker are live; the backend association label
        // exclusion remains deferred at the exact Konclude predicate.
        //   visited = false; continueVisiting = true;
        //   depTrackPoint = calcAlgContext->getBaseDependencyNode()->getContinueDependencyTrackPoint();
        //   backendSyncData = indiNode->getIndividualBackendCacheSynchronisationData(false);
        //   if backendSyncData: continueVisiting = visitFunc(indiNode, indiNode, depTrackPoint); visited = true;
        //   baseIndiId = indiNode->getNominalIndividual()->getIndividualID();
        //   mergingHash = indiNode->getIndividualMergingHash(false);
        //   if mergingHash:
        //     assocData = backendSyncData->getAssocitaionData();
        //     detSameIndiSetLabel = assocData ? assocData->getDeterministicMergedSameConsideredLabelCacheEntry() : null;
        //     for (mergedIndiId, mergingData) in mergingHash while continueVisiting:
        //       if baseIndiId != mergedIndiId && mergingData.isMergedWithIndividual()
        //          && !mBackendCacheHandler->hasIndividualIdsInAssociatedIndividualSetLabel(
        //                 assocData, detSameIndiSetLabel, mergedIndiId):
        //         backSyncDepTrackPoint = mergingData.getDependencyTrackPoint();
        //         backendSyncDataIndiNode = getUpToDateIndividual(-mergedIndiId, ctx);
        //         if backendSyncDataIndiNode->getIndividualBackendCacheSynchronisationData(false):
        //           locNode = localize ? getLocalizedIndividual(backendSyncDataIndiNode, false, ctx)
        //                              : backendSyncDataIndiNode;
        //           continueVisiting = visitFunc(indiNode, locNode, backSyncDepTrackPoint); visited = true;
        //   return visited;
        // W6-DEFER[api]: assocData->getDeterministicMergedSameConsideredLabelCacheEntry()
        // and mBackendCacheHandler->hasIndividualIdsInAssociatedIndividualSetLabel(...).
        // The old CIndividualMergingHash iteration is represented here by the
        // backend-sync merged-node linker, which is the live process satellite used
        // by the adjacent Unit 20/25 backend-sync ports.
        let base_dep_node = calc_alg_context.base_dependency_node();
        let dep_track_point = if base_dep_node.is_some() {
            calc_alg_context
                .process_context_mut()
                .materialize_continue_dependency_track_point(base_dep_node)
        } else {
            TrackPointId::NONE
        };
        let backend_sync_data = calc_alg_context
            .process_context()
            .node(indi_node)
            .individual_backend_cache_synchronisation_data(false);
        let mut visited = false;
        let mut continue_visiting = true;

        if backend_sync_data.is_some() {
            continue_visiting = visit_func(indi_node, indi_node, dep_track_point);
            visited = true;
        }

        if continue_visiting && backend_sync_data.is_some() {
            let merged_nodes = calc_alg_context
                .process_context()
                .backend_sync_data(backend_sync_data)
                .get_merged_individual_node_linker()
                .to_vec();
            for backend_sync_data_indi_node in merged_nodes {
                if !continue_visiting {
                    break;
                }
                if backend_sync_data_indi_node == indi_node {
                    continue;
                }
                let merged_backend_sync_data = calc_alg_context
                    .process_context()
                    .node(backend_sync_data_indi_node)
                    .individual_backend_cache_synchronisation_data(false);
                if merged_backend_sync_data.is_none() {
                    continue;
                }
                let loc_node = if localize {
                    self.get_localized_individual(
                        backend_sync_data_indi_node,
                        false,
                        calc_alg_context,
                    )
                } else {
                    backend_sync_data_indi_node
                };
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
                            .unwrap_or(dep_track_point)
                    } else {
                        dep_track_point
                    }
                };
                continue_visiting = visit_func(indi_node, loc_node, back_sync_dep_track_point);
                visited = true;
            }
        }

        visited
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::getBackendSynchronizationFilledRoleNeighbourExpansionDataHash`.
    /// cpp 23738–23772.
    ///
    /// Lazily builds (on the localised sync data) the per-(role, inversed) neighbour
    /// expansion data hash from the association data's role-set neighbour array.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: `assocData`, `locBackendSyncData`, and the
    /// returned per-role-neighbour expansion hash are all not-yet-ported
    /// backend-cache types → opaque `Cint64`.
    pub fn get_backend_synchronization_filled_role_neighbour_expansion_data_hash(
        &mut self,
        indi_node: NodeId,
        assoc_data: Cint64,
        loc_backend_sync_data: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> Cint64 {
        // PORT-PENDING: faithful transcription of cpp 23738–23772.
        //   roleNeighbourExpansionDataHash = locBackendSyncData->getRoleNeighbourExpansionDataHash(false);
        //   if !roleNeighbourExpansionDataHash:
        //     roleNeighbourExpansionDataHash = locBackendSyncData->getRoleNeighbourExpansionDataHash(true);
        //     neighbourRoleSetArray = assocData->getRoleSetNeighbourArray();
        //     if neighbourRoleSetArray:
        //       indexData = neighbourRoleSetArray->getIndexData();
        //       for i in 0..indexData->getArraySize():
        //         neighbourRoleSetlabel = indexData->getNeighbourRoleSetLabel(i);
        //         neighbourRoleSetArray->at(i).visitNeighbourIndividualIds(|indiId| {
        //           mBackendCacheHandler->visitRolesOfAssociatedNeigbourRoleSetLabel(
        //               assocData, neighbourRoleSetlabel,
        //               |role, inversed, aboxAsserted, nominalConnection, nondeterministic| {
        //             data = roleNeighbourExpansionDataHash[(role, inversed)];
        //             if nondeterministic: data.setPossiblyNondeterministicallyInstantiated(true);
        //             if !inversed: data.addIndividualIdLinker(new CXLinker<cint64>(indiId));
        //             true });
        //           true });
        //   return roleNeighbourExpansionDataHash;
        // W6-DEFER[api]: the role-set neighbour array, the label cache items, and
        // mBackendCacheHandler->visitRolesOfAssociatedNeigbourRoleSetLabel are not
        // yet ported.
        let _ = (
            indi_node,
            assoc_data,
            loc_backend_sync_data,
            calc_alg_context,
        );
        INVALID
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::getLocalizedIndividualBackendCacheSnychronisationData`.
    /// cpp 23984–23993.
    ///
    /// Returns the node's LOCAL backend-cache synchronisation data, lazily creating
    /// it (cloned from the shared/prev sync data) on first request.
    pub fn get_localized_individual_backend_cache_snychronisation_data(
        &mut self,
        indi_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> BackendSyncDataId {
        // `backendSyncData = indiNode->getIndividualBackendCacheSynchronisationData(false);`
        let backend_sync_data = calc_alg_context
            .process_context()
            .node(indi_node)
            .individual_backend_cache_synchronisation_data(false);
        // `locBackendSyncData = indiNode->getIndividualBackendCacheSynchronisationData(true);`
        let mut loc_backend_sync_data = calc_alg_context
            .process_context()
            .node(indi_node)
            .individual_backend_cache_synchronisation_data(true);
        if loc_backend_sync_data == Id::NONE {
            loc_backend_sync_data = calc_alg_context
                .process_context_mut()
                .alloc_backend_sync_data_from_prev(backend_sync_data);
            calc_alg_context
                .process_context_mut()
                .node_mut(indi_node)
                .set_individual_backend_cache_synchronisation_data(loc_backend_sync_data);
        }
        loc_backend_sync_data
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::testIndividualNodeBackendCacheNominalIndirectConnectionBlockingCritical`.
    /// cpp 25891–26001.
    ///
    /// Decides whether the node's indirectly-connected-nominal expansion is
    /// blocking-critical: re-tests new mergings, checks whether every indirectly
    /// connected nominal is already in the associated same-individual set label,
    /// and (if not) whether the unexpanded ATMOST/ATLEAST successors force an
    /// indirect-connected-individual expansion.
    pub fn test_individual_node_backend_cache_nominal_indirect_connection_blocking_critical(
        &mut self,
        indi_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // PORT-PENDING: faithful transcription of cpp 25891–26001 (111 lines). The
        // body is wholly backend-cache driven (W6-DEFER[api]); outline:
        //
        //   nominalIndirectExpansionBlockingCritical = false;
        //   backendSyncData = indiNode->getIndividualBackendCacheSynchronisationData(false);
        //   assocData       = backendSyncData->getAssocitaionData();
        //   locBackendSyncData = indiNode->getIndividualBackendCacheSynchronisationData(true);
        //   if backendSyncData:
        //     if !backendSyncData->isCriticalIndirectConnectionIndividualExpansionBlocking() && assocData:
        //       requiredIndirectConnectedIndividualExpansion = false;
        //       testIndividualNodeBackendCacheNewMergings(indiNode, ctx);              // merge unit
        //       backendSyncData = indiNode->getIndividualBackendCacheSynchronisationData(false);
        //       indirectlyConnectedNominalIndividual =
        //           (assocData && assocData->isIndirectlyConnectedNominalIndividual())
        //           || backendSyncData->hasMergedIndirectlyConnectedNominalIndividuals();
        //
        //       // (A) newly-merged-nodes pass:
        //       if backendSyncData->getMergedIndividualNodeLinker()
        //            != backendSyncData->getLastIndirectlyConnectedNominalIndividualsTestedMergedNodeLinker():
        //         nondetSameIndiSetLabel = assocData
        //             ? assocData->getLabelCacheEntry(NONDETERMINISTIC_SAME_INDIVIDUAL_SET_LABEL) : null;
        //         visitNewlyMergedOnlyDeterministicRepresentativeIndividualsBackendSynchronisationData(
        //             indiNode, mergedLinker, lastTestedLinker, false,
        //             |base, locNode, depTP| {                                          // merge unit visitor
        //               mergedBackendSyncData = locNode->getIndividualBackendCacheSynchronisationData(false);
        //               mergedAssocData = mergedBackendSyncData->getAssocitaionData();
        //               if mergedAssocData->isIndirectlyConnectedNominalIndividual():
        //                   indirectlyConnectedNominalIndividual = true;
        //               if !mBackendCacheHandler->hasIndividualIdsInAssociatedIndividualSetLabel(
        //                       assocData, nondetSameIndiSetLabel, locNode->getNominalIndividual()->getIndividualID()):
        //                   requiredIndirectConnectedIndividualExpansion = true; return false;
        //               return true; }, ctx);
        //         locBackendSyncData = getLocalizedIndividualBackendCacheSnychronisationData(indiNode, ctx); // this unit
        //         locBackendSyncData->setLastIndirectlyConnectedNominalIndividualsTestedMergedNodeLinker(mergedLinker);
        //         if indirectlyConnectedNominalIndividual:
        //             locBackendSyncData->setMergedIndirectlyConnectedNominalIndividuals(true);
        //
        //       // (B) relevant-sync-data pass (only if indirectly connected and not already required):
        //       if indirectlyConnectedNominalIndividual && !requiredIndirectConnectedIndividualExpansion:
        //         conSet = indiNode->getReapplyConceptLabelSet(false);
        //         if conSet:
        //           conDesLinker = conSet->getAddingSortedConceptDescriptionLinker();
        //           lastAddedLinkEdge = indiNode->getLastAddedRoleLink();
        //           visitIndividualsRelevantBackendSynchronisationDataIndividuals(indiNode, false,   // this unit
        //             |base, locNode, depTP| {
        //               backendSyncData = indiNode->getIndividualBackendCacheSynchronisationData(false);
        //               assocData = backendSyncData->getAssocitaionData();
        //               if assocData && assocData->isIndirectlyConnectedNominalIndividual():
        //                 lastTestedConDes = backendSyncData->getLastIndirectConnectedIndividualExpansionTestedConceptDescriptor();
        //                 lastTestedLinkEdge = backendSyncData->getLastIndirectConnectedIndividualExpansionTestedLinkEdge();
        //                 if lastAddedLinkEdge != lastTestedLinkEdge: lastTestedConDes = null;
        //                 if assocData->getLabelCacheEntry(FULL_CONCEPT_SET_LABEL)->hasNondeterministicElements()
        //                    || !testIndividualNodeBackendCacheConceptsSynchronization(indiNode, ctx):  // cache unit
        //                     requiredIndirectConnectedIndividualExpansion = true;
        //                 else:
        //                   for conDesIt = conDesLinker; conDesIt && conDesIt != lastTestedConDes
        //                                   && !required; conDesIt = conDesIt->getNext():
        //                     concept = conDesIt->getConcept(); conNegation = conDesIt->getNegation();
        //                     conOperator = concept->getConceptOperator(); role = concept->getRole();
        //                     if (!conNegation && conOperator has CCF_ATMOST)
        //                        || (conNegation && conOperator has CCF_ATLEAST):
        //                       for succLink in indiNode->getRoleSuccessorLinkIterator(role):
        //                         succ = getSuccessorIndividual(indiNode, succLink, ctx);
        //                         if succ->isNominalIndividualNode()
        //                            && succ->getIndividualNominalLevelOrAncestorDepth() > 0
        //                            && !succ->getNominalIndividual():
        //                             required = true;
        //                 locBackendSyncData = getLocalizedIndividualBackendCacheSnychronisationData(indiNode, ctx);
        //                 backendSyncData->setLastIndirectConnectedIndividualExpansionTestedLinkEdge(lastAddedLinkEdge);
        //                 backendSyncData->setLastIndirectConnectedIndividualExpansionTestedConceptDescriptor(conDesLinker);
        //               return !required; }, ctx);
        //
        //       // (C) commit criticality:
        //       if indirectlyConnectedNominalIndividual && requiredIndirectConnectedIndividualExpansion:
        //         locBackendSyncData = getLocalizedIndividualBackendCacheSnychronisationData(indiNode, ctx);
        //         locBackendSyncData->setCriticalIndirectConnectionIndividualExpansionBlocking(true);
        //         nominalIndirectExpansionBlockingCritical = true;
        //     else:
        //       nominalIndirectExpansionBlockingCritical = true;
        //   return nominalIndirectExpansionBlockingCritical;
        //
        // Held PORT-PENDING: every typed local is a not-yet-ported backend-cache
        // class (sync data, association data, label cache items, merged-node
        // linkers); the concept-operator ATMOST/ATLEAST scan + role-successor
        // iteration is portable but only reached through that backend-cache state.
        let _ = (indi_node, calc_alg_context);
        false
    }
}

#[cfg(test)]
mod tests {
    use super::super::super::model::concept::Concept;
    use super::super::super::model::individual::Individual;
    use super::super::super::model::substrate::INVALID;
    use super::super::super::model::VariableId;
    use super::super::super::process::backend_sync::IndividualNodeBackendCacheSynchronisationData;
    use super::super::super::process::context::ProcessContext;
    use super::super::super::process::merging_hash::IndividualMergingHash;
    use super::super::super::process::node::IndividualProcessNode;
    use super::super::super::process::varbind::{
        RepresentativeVariableBindingPathMapData, VarBindingDescriptorId, VarBindingPathId,
        VariableBinding, VariableBindingDescriptor, VariableBindingPath,
    };
    use super::super::super::process::NodeId;
    use super::super::super::process::TrackPointId;
    use super::super::algorithm::CompletionTaskHandleAlgorithm;
    use super::*;

    fn seed_backend_sync_data(
        ctx: &mut CalculationAlgorithmContextBase,
        node: NodeId,
    ) -> BackendSyncDataId {
        let data = IndividualNodeBackendCacheSynchronisationData::new();
        let sync = ctx.process_context_mut().alloc_backend_sync_data(data);
        ctx.process_context_mut()
            .node_mut(node)
            .set_individual_backend_cache_synchronisation_data(sync);
        sync
    }

    fn var_binding(
        ctx: &mut ProcessContext,
        variable: Cint64,
        individual: Cint64,
    ) -> super::super::super::process::varbind::VarBindingId {
        let id = ctx.alloc_var_binding(VariableBinding::new());
        ctx.var_binding_mut(id).init_variable_binding(
            TrackPointId::NONE,
            NodeId::new(individual),
            VariableId::new(variable),
        );
        id
    }

    fn var_binding_path_from_bindings(
        ctx: &mut ProcessContext,
        prop_id: Cint64,
        bindings: &[super::super::super::process::varbind::VarBindingId],
    ) -> VarBindingPathId {
        let mut head = VarBindingDescriptorId::NONE;
        let mut last = VarBindingDescriptorId::NONE;
        for binding in bindings {
            let des = ctx.alloc_var_binding_des(VariableBindingDescriptor::new());
            ctx.var_binding_des_mut(des)
                .init_variable_binding_descriptor(*binding);
            if last.is_some() {
                ctx.var_binding_des_mut(last).set_next(des);
            } else {
                head = des;
            }
            last = des;
        }
        let path = ctx.alloc_vbpath(VariableBindingPath::new());
        ctx.vbpath_mut(path)
            .init_variable_binding_path(prop_id, head);
        path
    }

    #[test]
    fn representative_joining_key_data_builds_cached_key_map() {
        let mut algo = CompletionTaskHandleAlgorithm::new();
        let mut calc_ctx = CalculationAlgorithmContextBase::new();
        let join_concept = {
            let mut concept = Concept::new();
            concept.add_variable_linker(VariableId::new(2));
            concept.add_variable_linker(VariableId::new(3));
            calc_ctx.ontology_arenas_mut().alloc_concept(concept)
        };

        let rep_data = {
            let tag = calc_ctx
                .process_context()
                .used_process_tagger()
                .get_current_localization_tag();
            let rep_data = calc_ctx
                .process_context_mut()
                .alloc_rep_var_bind_path_set_data(RepresentativeVariableBindingPathSetData::new(
                    INVALID, tag,
                ));
            calc_ctx
                .process_context_mut()
                .rep_var_bind_path_set_data_mut(rep_data)
                .set_representative_id(10);
            rep_data
        };

        let (path1, path2) = {
            let ctx = calc_ctx.process_context_mut();
            let b1 = var_binding(ctx, 1, 101);
            let b2 = var_binding(ctx, 2, 102);
            let b3 = var_binding(ctx, 3, 103);
            (
                var_binding_path_from_bindings(ctx, 41, &[b1, b2, b3]),
                var_binding_path_from_bindings(ctx, 42, &[b1, b2, b3]),
            )
        };

        let migrate_data = RepresentativeVariableBindingPathSetData::get_migrate_data(
            calc_ctx.process_context_mut(),
            rep_data,
            true,
        );
        {
            let map = calc_ctx
                .process_context_mut()
                .rep_var_bind_path_set_migrate_data_mut(migrate_data)
                .get_representative_variable_binding_path_map_mut();
            map.insert(
                41,
                RepresentativeVariableBindingPathMapData::new(path1, rep_data),
            );
            map.insert(
                42,
                RepresentativeVariableBindingPathMapData::new(path2, rep_data),
            );
        }

        let first_map =
            algo.get_representative_joining_key_data(rep_data, join_concept, &mut calc_ctx);
        assert_eq!(first_map.count(), 1);
        let bucket = first_map
            .get_joining_key_data_map_existing(1)
            .expect("first interned joining key bucket");
        assert_eq!(bucket.count(), 2);
        assert_eq!(bucket.value(41), path1);
        assert_eq!(bucket.value(42), path2);

        let second_map =
            algo.get_representative_joining_key_data(rep_data, join_concept, &mut calc_ctx);
        assert_eq!(second_map.count(), 1);
        assert_eq!(
            calc_ctx
                .process_context()
                .rep_var_bind_path_joining_key_hash(
                    calc_ctx
                        .processing_data_box()
                        .use_rep_var_bind_path_joining_key_hash
                )
                .next_rep_var_bind_path_joining_key_tag,
            2
        );
    }

    #[test]
    fn visit_relevant_backend_sync_individuals_uses_merging_hash_dependency_track_point() {
        let mut algo = CompletionTaskHandleAlgorithm::new();
        let mut calc_ctx = CalculationAlgorithmContextBase::new();

        let base_individual = calc_ctx
            .ontology_arenas_mut()
            .alloc_individual(Individual::new(10));
        let merged_individual = calc_ctx
            .ontology_arenas_mut()
            .alloc_individual(Individual::new(20));
        let base = calc_ctx
            .process_context_mut()
            .alloc_node(IndividualProcessNode::new(Id::NONE));
        let merged = calc_ctx
            .process_context_mut()
            .alloc_node(IndividualProcessNode::new(Id::NONE));
        calc_ctx
            .process_context_mut()
            .node_mut(base)
            .set_nominal_individual(base_individual);
        calc_ctx
            .process_context_mut()
            .node_mut(merged)
            .set_nominal_individual(merged_individual);

        let base_sync = seed_backend_sync_data(&mut calc_ctx, base);
        seed_backend_sync_data(&mut calc_ctx, merged);
        calc_ctx
            .process_context_mut()
            .backend_sync_data_mut(base_sync)
            .merged_individual_node_linker = vec![merged];

        let merge_track_point = TrackPointId::new(77);
        let mut merging_hash = IndividualMergingHash::new();
        merging_hash
            .entry_mut(20)
            .set_merged_with_individual(true)
            .set_dependency_track_point(merge_track_point);
        let merging_hash = calc_ctx
            .process_context_mut()
            .alloc_individual_merging_hash(merging_hash);
        calc_ctx
            .process_context_mut()
            .node_mut(base)
            .use_individual_merging_hash = merging_hash;

        let mut seen = Vec::new();
        assert!(
            algo.visit_individuals_relevant_backend_synchronisation_data_individuals(
                base,
                false,
                &mut |_, node, dep_track_point| {
                    seen.push((node, dep_track_point));
                    true
                },
                &mut calc_ctx,
            )
        );

        assert_eq!(
            seen,
            vec![(base, TrackPointId::NONE), (merged, merge_track_point)]
        );
    }
}
