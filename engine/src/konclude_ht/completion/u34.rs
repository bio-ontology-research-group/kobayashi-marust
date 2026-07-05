//! `completion::u34` — W3 completion method-batch **Unit 34**
//! (family: Generic helpers / accessors / label tests).
//!
//! Faithful function-by-function port of the 18 methods of Konclude
//! `CCalculationTableauCompletionTaskHandleAlgorithm`
//! (`Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.cpp`)
//! that `manifest/01-completion-methods.md` Unit 34 groups under generic
//! helpers / accessors / label tests. Method order follows the manifest
//! (ascending `.cpp` line). cpp line ranges (1-based) are noted on each item:
//!
//!   * `propagateFreshPropagationBindings`                       [13804-13871]
//!   * `addReverseRoleAssertion`                                 [14410-14455]
//!   * `addRoleAssertion`                                        [14495-14540]
//!   * `hasIdenticalConceptOperands`                             [14823-14858]
//!   * `createDistinctBranchingTask`                             [15530-15607]
//!   * `getAdditionalDisjunctCheckingConcept`                    [16464-16490]
//!   * `isConceptAdditionAtomaric`                               [17013-17019]
//!   * `installConceptRoleBranchTrigger`                         [17206-17217]
//!   * `searchNextConceptRoleBranchTrigger`                      [17221-17240]
//!   * `getIndividualNodeLink`                                   [17307-17319]
//!   * `isLabelConceptSubSet`                                    [17466-17543]
//!   * `isLabelConceptEqualSet`                                  [17547-17575]
//!   * `isPairwiseLabelConceptEqualSet`                          [17642-17695]
//!   * `collectIndividualNodeVariablePropagationBindings`       [18055-18084]
//!   * `getIndividualNodeAssociatedConceptsSetFromVariablePropagationBindings`     [18102-18114]
//!   * `getIndividualNodesListAssociatedConceptsSetFromVariablePropagationBindings`[18120-18149]
//!   * `isAnonymousVariablePropagationBindingSingleIndividualAnalogousPath`        [18155-18258]
//!   * `isAnonymousVariablePropagationBindingAnalogousPath`     [18283-18383]
//!
//! Bodies use the W3.5 accessor convention (PORT.md): a C++ `indi->getX()` where
//! `indi` is a `CIndividualProcessNode*` becomes `ctx.process_context().node(id).get_x()`
//! (read) / `ctx.process_context_mut().node_mut(id)` (mutate); `getProcessingDataBox()`
//! → `ctx.processing_data_box{,_mut}()`; terminology (`CConcept`/`CRole`) via
//! `ctx.ontology_arenas()`; sibling algorithm methods → `self.x(...)`.
//!
//! KONCLUDE-PORT-NOTE[ownership]: pointers become arena ids (`CIndividualProcessNode*`
//! → `NodeId`, `CConcept*` → `ConceptId`, `CRole*` → `RoleId`,
//! `CConceptDescriptor*` → `ConDescId`, `CDependencyTrackPoint*` → `TrackPointId`,
//! `CIndividualLinkEdge*` → `EdgeId`); a `CIndividualProcessNode*&` out/in-out
//! reference becomes `&mut NodeId`; the `calcAlgContext` pointer becomes the
//! threaded `&mut CalculationAlgorithmContextBase`.
//!
//! Three methods are FULLY PORTED (they bottom out only on the ported concept/role
//! model): `hasIdenticalConceptOperands`, `getAdditionalDisjunctCheckingConcept`,
//! `isConceptAdditionAtomaric`. The remainder sit on top of not-yet-ported
//! subsystems — the propagation-/variable-binding type web
//! (`CPropagationBindingSet`/`Map`/`Descriptor`, `CConceptVariableBindingPathSetHash`,
//! `CVariableBindingPath`, `CBlockingVariableBindingsAnalogousPropagationData`),
//! the per-node satellite hashes (`CReapplyConceptLabelSet` iterators,
//! `CReapplyRoleSuccessorHash`, `CSuccessorRoleHash`, `CIndividualMergingHash`,
//! `CSuccessorConnectedNominalSet`), the role/reverse-role assertion linkers, the
//! concept-role branching trigger, and the merge/branching task machinery. Per the
//! port convention their control flow is reproduced faithfully with the unported
//! dereferences marked `// W6-DEFER[api]` / `// W3-DEFER[...]` (logic in-comment,
//! never dropped); the genuinely entangled task-creation / binding-propagation
//! bodies are held `// PORT-PENDING` with a structural transcription.

#![allow(dead_code)]
#![allow(unused_variables)]

use super::super::model::op::{CCAQCHOOCE, CCATOM, CCIMPLTRIG, CCSUB};
use super::super::model::substrate::{Cint64, Id, NegLink, INVALID};
use super::super::model::{ConceptId, IndividualId, RoleId};
use super::super::process::propagation_binding::{
    PropagationBindingDescriptor, PropagationBindingDescriptorId, PropagationBindingMapData,
    PropagationBindingSet, PropagationBindingSetId,
};
use super::super::process::stubs::IndiBlockDataId;
use super::super::process::varbind::VarBindingPathId;
use super::super::process::{
    ConDescId, ConProcDescId, DepLinkId, DependencyId, EdgeId, LabelSetId, NodeId,
    RestrictionSpecId, TrackPointId,
};
use super::context::CalculationAlgorithmContextBase;
use super::stubs::SatisfiableCalculationTask;

/// KONCLUDE-PORT-NOTE[ownership]: `CDependency*` additional-dependency chains are
/// represented by the folded dependency-link spine used by the dependency factory.
type DependencyHandle = DepLinkId;
/// KONCLUDE-PORT-NOTE[api]: `CProcessingRestrictionSpecification*` is not yet ported
/// → opaque handle.
type ProcRestrictionHandle = Cint64;
/// KONCLUDE-PORT-NOTE[api]: `CConceptRoleBranchingTrigger*` is not yet ported →
/// opaque handle (chain walked via the deferred `getNextBranchingTrigger`).
type BranchingTriggerHandle = Cint64;
/// KONCLUDE-PORT-NOTE[api]: `CReverseRoleAssertionLinker*` / `CRoleAssertionLinker*`
/// are not yet ported (assertion-linker satellites) → opaque handles.
type RoleAssertionLinkerHandle = Cint64;
/// KONCLUDE-PORT-NOTE[ownership]: `CVariableBindingPath*` → `VarBindingPathId`.
type VariableBindingPathHandle = VarBindingPathId;
/// KONCLUDE-PORT-NOTE[api]: `CIndividualNodeBlockingTestData*` /
/// `CBlockingAlternativeData**` (blocking-test satellites) are not yet ported.
type BlockingTestDataHandle = Cint64;

impl super::algorithm::CompletionTaskHandleAlgorithm {
    // =======================================================================
    // Fresh propagation-binding propagation (cpp 13804-13871).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::propagateFreshPropagationBindings`.
    /// cpp 13804-13871.
    ///
    /// The propagation-binding twin of `propagate_fresh_variable_bindings` (u11):
    /// merge-walks the previous and new propagation-binding maps (sorted by
    /// propagation id) and, for every prev-only / not-yet-described key, allocates a
    /// fresh `CPropagationBindingDescriptor` carrying a `PROPAGATEBINDING` dependency
    /// and re-applies any queued reapply concepts.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: `newPropBindingSet`/`prevPropBindingSet`
    /// (`CPropagationBindingSet*`) are arena ids; `otherDependencies`
    /// (`CDependency*`) is represented by the folded `DepLinkId` dependency spine.
    pub fn propagate_fresh_propagation_bindings(
        &mut self,
        process_indi: &mut NodeId,
        con_des: ConDescId,
        new_prop_binding_set: PropagationBindingSetId,
        prev_prop_binding_set: PropagationBindingSetId,
        other_dependencies: DependencyHandle,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W3-DEFER[memory-pool]: taskMemMan = calcAlgContext->getUsedProcessTaskMemoryAllocationManager()
        let task_mem_man: Cint64 = INVALID;
        let mut propagations = false;
        if prev_prop_binding_set.is_some() {
            let adopted = {
                let prev_snapshot = {
                    let pc = calc_alg_context.process_context();
                    pc.prop_binding_set(prev_prop_binding_set)
                        .propagate_all_flag
                };
                let new_set = calc_alg_context
                    .process_context_mut()
                    .prop_binding_set_mut(new_prop_binding_set);
                let old_flag = new_set.propagate_all_flag;
                new_set.propagate_all_flag |= prev_snapshot;
                new_set.propagate_all_flag != old_flag
            };
            propagations |= adopted;

            let prop_keys: Vec<(Cint64, bool)> = {
                let pc = calc_alg_context.process_context();
                let prev_map = &pc.prop_binding_set(prev_prop_binding_set).prop_map.map;
                let new_map = &pc.prop_binding_set(new_prop_binding_set).prop_map.map;
                let mut keys = Vec::new();
                for (&prev_prop_id, prev_data) in prev_map.iter() {
                    if !prev_data.has_propagation_binding_descriptor() {
                        continue;
                    }
                    let update_existing = new_map
                        .get(&prev_prop_id)
                        .map_or(false, |data| !data.has_propagation_binding_descriptor());
                    if !new_map.contains_key(&prev_prop_id) || update_existing {
                        keys.push((prev_prop_id, update_existing));
                    }
                }
                keys.sort_by_key(|(prop_id, _)| *prop_id);
                keys
            };
            let mut new_prop_bind_des_linker: PropagationBindingDescriptorId = Id::NONE;
            for (prev_prop_id, update_existing) in prop_keys {
                // W3-DEFER[macro]: STATINC(PBINDPROPAGATEDCOUNT, calcAlgContext)
                // W3-DEFER[macro]: STATINC(PBINDPROPAGATEDFRESHCOUNT, calcAlgContext)
                let prev_prop_bind_des = calc_alg_context
                    .process_context()
                    .prop_binding_set(prev_prop_binding_set)
                    .prop_map
                    .value(prev_prop_id)
                    .get_propagation_binding_descriptor();
                let prop_binding = calc_alg_context
                    .process_context()
                    .prop_binding_des(prev_prop_bind_des)
                    .get_propagation_binding();
                let prev_dep_track_point = calc_alg_context
                    .process_context()
                    .prop_binding_des(prev_prop_bind_des)
                    .get_dependency_track_point();
                // W3-DEFER[memory-pool]: allocateAndConstruct<CPropagationBindingDescriptor>(taskMemMan)
                let new_prop_bind_des = calc_alg_context
                    .process_context_mut()
                    .alloc_prop_binding_des(PropagationBindingDescriptor::new());
                calc_alg_context
                    .process_context_mut()
                    .prop_binding_des_mut(new_prop_bind_des)
                    .set_data(new_prop_bind_des);
                let mut new_dep_track_point: TrackPointId = Id::NONE;
                let _bind_dep_node = self.create_propagate_binding_dependency(
                    &mut new_dep_track_point,
                    process_indi,
                    con_des,
                    prev_dep_track_point,
                    other_dependencies,
                    calc_alg_context,
                );
                if new_dep_track_point.is_none() {
                    new_dep_track_point = prev_dep_track_point;
                }
                calc_alg_context
                    .process_context_mut()
                    .prop_binding_des_mut(new_prop_bind_des)
                    .init_propagation_binding_descriptor(prop_binding, new_dep_track_point);
                if update_existing {
                    let reapply_des = {
                        let data = calc_alg_context
                            .process_context_mut()
                            .prop_binding_set_mut(new_prop_binding_set)
                            .prop_map
                            .entry_mut(prev_prop_id);
                        data.set_propagation_binding_descriptor(new_prop_bind_des);
                        data.get_reapply_concept_descriptor()
                    };
                    if reapply_des.is_some() {
                        self.apply_reapply_queue_concepts_propagation_binding(
                            *process_indi,
                            reapply_des,
                            calc_alg_context,
                        );
                    }
                } else {
                    calc_alg_context
                        .process_context_mut()
                        .prop_binding_set_mut(new_prop_binding_set)
                        .prop_map
                        .map
                        .insert(
                            prev_prop_id,
                            PropagationBindingMapData::new(new_prop_bind_des),
                        );
                }
                if new_prop_bind_des_linker.is_none() {
                    new_prop_bind_des_linker = new_prop_bind_des;
                } else {
                    PropagationBindingDescriptor::append(
                        calc_alg_context.process_context_mut(),
                        new_prop_bind_des,
                        new_prop_bind_des_linker,
                    );
                    new_prop_bind_des_linker = new_prop_bind_des;
                }
                propagations = true;
            }
            if new_prop_bind_des_linker.is_some() {
                PropagationBindingSet::add_propagation_binding_descriptor_linker(
                    calc_alg_context.process_context_mut(),
                    new_prop_binding_set,
                    new_prop_bind_des_linker,
                );
            }
        }
        let _ = (
            con_des,
            new_prop_binding_set,
            other_dependencies,
            task_mem_man,
        );
        propagations
    }

    // =======================================================================
    // Reverse / forward role-assertion materialisation (cpp 14410, 14495).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addReverseRoleAssertion`.
    /// cpp 14410-14455.
    ///
    /// Materialises an ABox role assertion where `process_indi` is the FILLER: looks
    /// up the asserted nominal individual node, and (unless the link already exists)
    /// creates the ROLEASSERTION dependency + the (reapplied) role link FROM the
    /// nominal TO `process_indi`. Under incremental compatible expansion of an
    /// unavailable nominal it instead pushes the role's domain concepts.
    pub fn add_reverse_role_assertion(
        &mut self,
        process_indi: &mut NodeId,
        reverse_role_assertion_linker: RoleAssertionLinkerHandle,
        dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[macro]: STATINC(REVERSEROLEASSERTIONCOUNT, calcAlgContext)
        // W6-DEFER[api]: role = reverseRoleAssertionLinker->getRole();
        //                indi = reverseRoleAssertionLinker->getIndividual();
        // (CReverseRoleAssertionLinker is an unported satellite linker.)
        let role: RoleId = Id::NONE;
        let indi: IndividualId = Id::NONE; // CIndividual* (asserted individual) — deferred id.
                                           // markIndividualNodeBackendNonConceptSetRelatedProcessing(processIndi, calcAlgContext)
        self.mark_individual_node_backend_non_concept_set_related_processing(
            *process_indi,
            calc_alg_context,
        );

        if indi != Id::NONE {
            // indiID = indi->getIndividualID(); the nominal node is keyed by -indiID.
            let nominal_id: Cint64 = INVALID; // -indi->getIndividualID()
            if !self.opt_incremental_compatible_expansion
                || self.is_nominal_individual_node_available(nominal_id, calc_alg_context)
            {
                // nominalIndi = getCorrectedNominalIndividualNode(-indi->getIndividualID(), ctx)
                let nominal_indi =
                    self.get_corrected_nominal_individual_node(nominal_id, calc_alg_context);
                // C++ guard: nominalIndi && (!nominalIndi->hasRoleAssertionsInitialized()
                //   || processIndi->getRoleAssertionCreationID() > nominalIndi->getRoleAssertionCreationID())
                // W6-DEFER[api]: hasRoleAssertionsInitialized / getRoleAssertionCreationID are
                //   not yet ported on IndividualProcessNode; the guard is held true so the
                //   create-link body is reached faithfully once those node accessors land.
                let guard_passes = nominal_indi != Id::NONE; // && (deferred init/creation-id test)
                if guard_passes {
                    // locNominalIndi = getLocalizedForcedBackendInitializedNominalIndividualNode(nominalIndi, ctx)
                    let mut loc_nominal_indi = self
                        .get_localized_forced_backend_initialized_nominal_individual_node(
                            nominal_indi,
                            calc_alg_context,
                        );
                    self.mark_individual_node_backend_non_concept_set_related_processing(
                        loc_nominal_indi,
                        calc_alg_context,
                    );

                    // nominalConDepTrackPoint = nullptr;
                    // if -indi->getIndividualID() != locNominalIndi->getIndividualNodeID():
                    //   nominalConDepTrackPoint =
                    //     locNominalIndi->getIndividualMergingHash(false)
                    //       ->value(indi->getIndividualID()).getDependencyTrackPoint();
                    // W6-DEFER[api]: getIndividualMergingHash is an unported node satellite.
                    let nominal_con_dep_track_point: TrackPointId = Id::NONE;

                    // if (!hasIndividualsLink(locNominalIndi, processIndi, role, true, ctx)):
                    if !self.has_individuals_link(
                        &mut loc_nominal_indi,
                        process_indi,
                        role,
                        true,
                        calc_alg_context,
                    ) {
                        // create dependency
                        let mut next_dep_track_point: TrackPointId = Id::NONE;
                        // roleAssDepNode = createROLEASSERTIONDependency(nextDepTrackPoint, processIndi,
                        //     depTrackPoint, nominalConDepTrackPoint, role, indi, calcAlgContext)
                        let _role_ass_dep_node = self.create_role_assertion_dependency(
                            &mut next_dep_track_point,
                            *process_indi,
                            dep_track_point,
                            nominal_con_dep_track_point,
                            role,
                            indi,
                            calc_alg_context,
                        );

                        // create link FROM the nominal TO processIndi
                        // createNewIndividualsLinksReapplyed(locNominalIndi, processIndi,
                        //     role->getIndirectSuperRoleList(), role, nextDepTrackPoint, true, ctx)
                        // W3-RECONCILE[ownership]: snapshot role->getIndirectSuperRoleList()
                        // before the &mut-ctx call (role_linker_it arg).
                        let super_role_list: Vec<super::super::model::substrate::NegLink<RoleId>> =
                            calc_alg_context
                                .ontology_arenas()
                                .role(role)
                                .get_indirect_super_role_list()
                                .to_vec();
                        self.create_new_individuals_links_reapplyed(
                            loc_nominal_indi,
                            *process_indi,
                            &super_role_list,
                            role,
                            next_dep_track_point,
                            true,
                            calc_alg_context,
                        );

                        self.propagate_individual_node_modified(
                            &mut loc_nominal_indi,
                            calc_alg_context,
                        );
                        self.add_individual_to_processing_queue(loc_nominal_indi, calc_alg_context);
                    }
                    let _ = &mut loc_nominal_indi;
                }
            } else if self.opt_incremental_compatible_expansion {
                // Nominal unavailable: push the role's DOMAIN concepts onto processIndi
                // for every (possibly inverse) indirect super-role.
                // for roleLinkerIt in role->getIndirectSuperRoleList():
                let super_roles: Vec<NegLink<RoleId>> = calc_alg_context
                    .ontology_arenas()
                    .role(role)
                    .get_indirect_super_role_list()
                    .to_vec();
                for role_linker in super_roles.iter() {
                    let super_role = role_linker.target;
                    let inv_role = role_linker.negated;
                    // domainConLinkerIt = role->getDomainRangeConceptList(!invRole)
                    let domain_cons: Vec<NegLink<ConceptId>> = calc_alg_context
                        .ontology_arenas()
                        .role(super_role)
                        .get_domain_range_concept_list(!inv_role)
                        .to_vec();
                    if !domain_cons.is_empty() {
                        // addConceptsToIndividual(domainConLinkerIt, false, processIndi,
                        //     depTrackPoint, true, false, nullptr, calcAlgContext)
                        self.add_concepts_to_individual(
                            &domain_cons,
                            false,
                            process_indi,
                            dep_track_point,
                            true,
                            false,
                            None,
                            calc_alg_context,
                        );
                    }
                }
            }
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addRoleAssertion`.
    /// cpp 14495-14540.
    ///
    /// The forward twin of `add_reverse_role_assertion`: `process_indi` is the
    /// SUBJECT; creates the (reapplied) role link FROM `process_indi` TO the asserted
    /// nominal node. Under incremental compatible expansion of an unavailable nominal
    /// it pushes the role's RANGE concepts instead.
    pub fn add_role_assertion(
        &mut self,
        process_indi: &mut NodeId,
        role_assertion_linker: RoleAssertionLinkerHandle,
        dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[macro]: STATINC(ROLEASSERTIONCOUNT, calcAlgContext)
        // W6-DEFER[api]: role = roleAssertionLinker->getRole();
        //                indi = roleAssertionLinker->getIndividual();
        let role: RoleId = Id::NONE;
        let indi: IndividualId = Id::NONE; // CIndividual* — deferred id.
        self.mark_individual_node_backend_non_concept_set_related_processing(
            *process_indi,
            calc_alg_context,
        );

        if indi != Id::NONE {
            let nominal_id: Cint64 = INVALID; // -indi->getIndividualID()
            if !self.opt_incremental_compatible_expansion
                || self.is_nominal_individual_node_available(nominal_id, calc_alg_context)
            {
                let nominal_indi =
                    self.get_corrected_nominal_individual_node(nominal_id, calc_alg_context);
                // C++ guard: nominalIndi && (!nominalIndi->hasReverseRoleAssertionsInitialized()
                //   || processIndi->getRoleAssertionCreationID() > nominalIndi->getRoleAssertionCreationID())
                // W6-DEFER[api]: hasReverseRoleAssertionsInitialized / getRoleAssertionCreationID
                //   are unported node accessors; guard held true to reach the body faithfully.
                let guard_passes = nominal_indi != Id::NONE;
                if guard_passes {
                    let mut loc_nominal_indi = self
                        .get_localized_forced_backend_initialized_nominal_individual_node(
                            nominal_indi,
                            calc_alg_context,
                        );
                    self.mark_individual_node_backend_non_concept_set_related_processing(
                        loc_nominal_indi,
                        calc_alg_context,
                    );

                    // nominalConDepTrackPoint = nullptr;
                    // if -indi->getIndividualID() != locNominalIndi->getIndividualNodeID()
                    //    && locNominalIndi->getIndividualMergingHash(false):
                    //   nominalConDepTrackPoint =
                    //     locNominalIndi->getIndividualMergingHash(false)
                    //       ->value(indi->getIndividualID()).getDependencyTrackPoint();
                    // W6-DEFER[api]: getIndividualMergingHash is an unported node satellite.
                    let nominal_con_dep_track_point: TrackPointId = Id::NONE;

                    // if (!hasIndividualsLink(processIndi, locNominalIndi, role, true, ctx)):
                    if !self.has_individuals_link(
                        process_indi,
                        &mut loc_nominal_indi,
                        role,
                        true,
                        calc_alg_context,
                    ) {
                        // create dependency
                        let mut next_dep_track_point: TrackPointId = Id::NONE;
                        // roleAssDepNode = createROLEASSERTIONDependency(nextDepTrackPoint, processIndi,
                        //     depTrackPoint, nominalConDepTrackPoint, role,
                        //     processIndi->getNominalIndividual(), calcAlgContext)
                        let process_nominal_individual = calc_alg_context
                            .process_context()
                            .node(*process_indi)
                            .nominal_individual();
                        let _role_ass_dep_node = self.create_role_assertion_dependency(
                            &mut next_dep_track_point,
                            *process_indi,
                            dep_track_point,
                            nominal_con_dep_track_point,
                            role,
                            process_nominal_individual,
                            calc_alg_context,
                        );

                        // create link FROM processIndi TO the nominal
                        // createNewIndividualsLinksReapplyed(processIndi, locNominalIndi,
                        //     role->getIndirectSuperRoleList(), role, nextDepTrackPoint, true, ctx)
                        // W3-RECONCILE[ownership]: snapshot role->getIndirectSuperRoleList()
                        // before the &mut-ctx call (role_linker_it arg).
                        let super_role_list: Vec<super::super::model::substrate::NegLink<RoleId>> =
                            calc_alg_context
                                .ontology_arenas()
                                .role(role)
                                .get_indirect_super_role_list()
                                .to_vec();
                        self.create_new_individuals_links_reapplyed(
                            *process_indi,
                            loc_nominal_indi,
                            &super_role_list,
                            role,
                            next_dep_track_point,
                            true,
                            calc_alg_context,
                        );

                        self.propagate_individual_node_modified(
                            &mut loc_nominal_indi,
                            calc_alg_context,
                        );
                        self.add_individual_to_processing_queue(loc_nominal_indi, calc_alg_context);
                    }
                    let _ = &mut loc_nominal_indi;
                }
            } else if self.opt_incremental_compatible_expansion {
                // Nominal unavailable: push the role's RANGE concepts onto processIndi
                // for every (possibly inverse) indirect super-role.
                let super_roles: Vec<NegLink<RoleId>> = calc_alg_context
                    .ontology_arenas()
                    .role(role)
                    .get_indirect_super_role_list()
                    .to_vec();
                for role_linker in super_roles.iter() {
                    let super_role = role_linker.target;
                    let inv_role = role_linker.negated;
                    // domainConLinkerIt = role->getDomainRangeConceptList(invRole)
                    let range_cons: Vec<NegLink<ConceptId>> = calc_alg_context
                        .ontology_arenas()
                        .role(super_role)
                        .get_domain_range_concept_list(inv_role)
                        .to_vec();
                    if !range_cons.is_empty() {
                        self.add_concepts_to_individual(
                            &range_cons,
                            false,
                            process_indi,
                            dep_track_point,
                            true,
                            false,
                            None,
                            calc_alg_context,
                        );
                    }
                }
            }
        }
    }

    // =======================================================================
    // Pure concept-operand helpers (cpp 14823, 16464, 17013) — FULLY PORTED.
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::hasIdenticalConceptOperands`.
    /// cpp 14823-14858.
    ///
    /// Tests two operand lists for set-equality of `(concept, negation)` pairs. A
    /// double-containment test (every operand of list 1 occurs in list 2 and vice
    /// versa), guarded by an equal-count fast fail — a faithful 1:1 translation, the
    /// intrusive `CSortedNegLinker<CConcept*>*` chains become `&[NegLink<ConceptId>]`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: the C++ method takes no `calcAlgContext`; neither does
    /// the port.
    pub fn has_identical_concept_operands(
        &self,
        op_con_linker1: &[NegLink<ConceptId>],
        op_con_linker2: &[NegLink<ConceptId>],
    ) -> bool {
        if op_con_linker1.len() != op_con_linker2.len() {
            return false;
        }
        for op1 in op_con_linker1.iter() {
            let con1 = op1.target;
            let neg1 = op1.negated;
            let mut found_operand = false;
            for op2 in op_con_linker2.iter() {
                if found_operand {
                    break;
                }
                if con1 == op2.target && neg1 == op2.negated {
                    found_operand = true;
                }
            }
            if !found_operand {
                return false;
            }
        }
        for op2 in op_con_linker2.iter() {
            let con1 = op2.target;
            let neg1 = op2.negated;
            let mut found_operand = false;
            for op1 in op_con_linker1.iter() {
                if found_operand {
                    break;
                }
                if con1 == op1.target && neg1 == op1.negated {
                    found_operand = true;
                }
            }
            if !found_operand {
                return false;
            }
        }
        true
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::getAdditionalDisjunctCheckingConcept`.
    /// cpp 16464-16490.
    ///
    /// For an `AQCHOOCE` (qualified-cardinality choose) operand concept whose operand
    /// list has EXACTLY ONE operand of the requested polarity, returns that operand
    /// as the additional disjunct checking concept (with negation `false`).
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: the C++ nullable out-pointers `CConcept**` /
    /// `bool*` become `Option<&mut ConceptId>` / `Option<&mut bool>` (the `if (ptr)`
    /// null-guards become `if let Some(..)`).
    pub fn get_additional_disjunct_checking_concept(
        &self,
        op_concept: ConceptId,
        op_con_negation: bool,
        checking_concept: Option<&mut ConceptId>,
        checking_negation: Option<&mut bool>,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        if calc_alg_context
            .ontology_arenas()
            .concept(op_concept)
            .get_operator_code()
            == CCAQCHOOCE
        {
            let mut replace_count: Cint64 = 0;
            let mut replace_checking_concept: ConceptId = Id::NONE;
            let operands: Vec<NegLink<ConceptId>> = calc_alg_context
                .ontology_arenas()
                .concept(op_concept)
                .get_operand_list()
                .to_vec();
            for op_op in operands.iter() {
                let op_op_concept = op_op.target;
                let op_op_negation = op_op.negated;
                if op_op_negation == op_con_negation {
                    replace_checking_concept = op_op_concept;
                    replace_count += 1;
                }
            }

            if replace_count == 1 && replace_checking_concept != Id::NONE {
                if let Some(out_neg) = checking_negation {
                    *out_neg = false;
                }
                if let Some(out_con) = checking_concept {
                    *out_con = replace_checking_concept;
                }
                return true;
            }
        }
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::isConceptAdditionAtomaric`.
    /// cpp 17013-17019.
    ///
    /// True iff adding `adding_concept` (with the given polarity) is "atomic" — a
    /// negated `SUB`/`IMPLTRIG` or any `ATOM`. The C++ operator-precedence grouping
    /// `negated && (a || b) || c` is preserved verbatim (Rust binds `&&` over `||`
    /// identically).
    pub fn is_concept_addition_atomaric(
        &self,
        adding_concept: ConceptId,
        negated: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let op_code = calc_alg_context
            .ontology_arenas()
            .concept(adding_concept)
            .get_operator_code();
        if negated && (op_code == CCSUB || op_code == CCIMPLTRIG) || op_code == CCATOM {
            return true;
        }
        false
    }

    // =======================================================================
    // Distinct-merge branching task (cpp 15530-15607).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::createDistinctBranchingTask`.
    /// cpp 15530-15607.
    ///
    /// Spawns a dependent branching task whose merging restriction keeps
    /// `distinct_indi_node` DISTINCT from the other merge candidates (creating it as
    /// an empty / nominal node when minimising merging or when forced), then re-queues
    /// the continuing merge concept under the cloned restriction and sets the new
    /// task's merge priority.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: `CNonDeterministicDependencyNode*` →
    /// `DependencyId`; the returned `CSatisfiableCalculationTask*` →
    /// `Id<SatisfiableCalculationTask>`.
    pub fn create_distinct_branching_task(
        &mut self,
        process_indi_node: &mut NodeId,
        con_pro_des: ConProcDescId,
        distinct_indi_node: &mut NodeId,
        create_as_nominal: bool,
        merge_dependency_node: DependencyId,
        branching_merging_proc_rest: RestrictionSpecId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> Id<SatisfiableCalculationTask> {
        // Faithful transcription of cpp 15530-15607. The branch-dependent task
        // allocation is live; the remaining branch-local body still depends on
        // not-yet-ported child context/databox/scheduler facilities:
        //
        //   STATINC(TASKDISTINCTMERGEBRANCHCREATIONCOUNT, calcAlgContext);
        //   conDes = conProDes->getConceptDescriptor();
        //   role   = conDes->getConcept()->getRole();
        let new_sat_calc_task = self.create_dependend_branching_task_list(1, calc_alg_context);
        //   newSatCalcTask = createDependendBranchingTaskList(1, calcAlgContext);
        //   processorContext = calcAlgContext->getUsedTaskProcessorContext();
        //   newProcessContext = newSatCalcTask->getProcessContext(processorContext);
        //   newCalcAlgContext = createCalculationAlgorithmContext(processorContext,
        //                           newProcessContext, newSatCalcTask);                      // W6-DEFER[api]
        //   newProcessingDataBox = newSatCalcTask->getProcessingDataBox();
        //   newTaskMemMan = newCalcAlgContext->getUsedProcessTaskMemoryAllocationManager();
        //   mergeNonDetDepTrackPoint =
        //       createNonDeterministicDependencyTrackPointBranch(mergeDependencyNode, false, newCalcAlgContext);
        //   newBranchingMergingProcRest =
        //       allocateAndConstructAndParameterize<CBranchingMergingProcessingRestrictionSpecification>(...);
        //   newBranchingMergingProcRest->initBranchingMergingProcessingRestriction(branchingMergingProcRest);
        //   newProcessTagger = newCalcAlgContext->getUsedProcessTagger();
        //   newProcessTagger->incBranchingTag(); newProcessTagger->incLocalizationTag();
        //   newLocDistinctIndiNode = getLocalizedIndividual(distinctIndiNode, false, newCalcAlgContext);
        //   locProcessIndiNode     = getLocalizedIndividual(processIndiNode, false, newCalcAlgContext);
        //   locDistinctMergedSet   = newBranchingMergingProcRest->getDistinctMergedNodesSet(true);
        //   if ((mConfMinimizeMerging || createAsNominal) && !newLocDistinctIndiNode->isNominalIndividualNode()):
        //       if createAsNominal: newBranchingMergingProcRest->decRemainingNominalCreationCount();
        //       mergedIntoEmptyIndiNode = getIntoEmptyMergedIndividualNode(newLocDistinctIndiNode,
        //                                     createAsNominal, processIndiNode, mergeNonDetDepTrackPoint, newCalcAlgContext);
        //       locDistinctMergedSet->insert(mergedIntoEmptyIndiNode->getIndividualNodeID());
        //       roleSuccIt = locProcessIndiNode->getRoleSuccessorHistoryLinkIterator(role,
        //                        newBranchingMergingProcRest->getLastIndividualLink());
        //       if roleSuccIt.hasNext(): newBranchingMergingProcRest->setLastIndividualLink(roleSuccIt.next());
        //       addIndividualToProcessingQueue(mergedIntoEmptyIndiNode, newCalcAlgContext);
        //   else:
        //       newBranchingMergingProcRest->initMergingDependencyNode(mergeDependencyNode);
        //       newBranchingMergingProcRest->initDependencyTracker(mergeNonDetDepTrackPoint);
        //       locDistinctMergedSet->insert(newLocDistinctIndiNode->getIndividualNodeID());
        //   if newBranchingMergingProcRest->isDistinctSetNodeRelocated():
        //       newBranchingMergingProcRest->setDistinctSetNodeRelocated(false);
        //       newBranchingMergingProcRest->initMergingDependencyNode(mergeDependencyNode);
        //       newBranchingMergingProcRest->initDependencyTracker(mergeNonDetDepTrackPoint);
        //   conProQueu = locProcessIndiNode->getConceptProcessingQueue(true);
        //   addConceptRestrictedToProcessingQueue(conDes, mergeNonDetDepTrackPoint, conProQueu,
        //       locProcessIndiNode, true, newBranchingMergingProcRest, newCalcAlgContext);
        //   prepareBranchedTaskProcessing(locProcessIndiNode, newSatCalcTask, newCalcAlgContext);
        //   newTaskPriority = calcAlgContext->getUsedTaskPriorityStrategy()
        //       ->getPriorityForTaskMerging(newSatCalcTask, calcAlgContext->getUsedSatisfiableCalculationTask());
        //   newSatCalcTask->setTaskPriority(newTaskPriority);
        //   return newSatCalcTask;
        //
        // Held partially deferred because the new per-task context/databox/memory
        // pool come from the still-deferred `createCalculationAlgorithmContext`,
        // and every typed local belongs to a not-yet-ported class (process tagger,
        // task processor context, the new branching-merging restriction spec on
        // the NEW context).
        let _ = (
            process_indi_node,
            con_pro_des,
            distinct_indi_node,
            create_as_nominal,
            merge_dependency_node,
            branching_merging_proc_rest,
            &mut *calc_alg_context,
        );
        if let Some(task_priority_strategy) = calc_alg_context.base.used_task_priority_strategy() {
            let used_sat_calc_task = calc_alg_context.base.used_sat_calc_task;
            let new_task_priority = task_priority_strategy.get_priority_for_task_merging(
                &calc_alg_context.base.sat_calc_task_arena,
                new_sat_calc_task,
                used_sat_calc_task,
            );
            calc_alg_context
                .base
                .sat_calc_task_mut(new_sat_calc_task)
                .base
                .set_task_priority(new_task_priority);
        }
        new_sat_calc_task
    }

    // =======================================================================
    // Concept-role branching triggers (cpp 17206, 17221).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::installConceptRoleBranchTrigger`.
    /// cpp 17206-17217.
    ///
    /// Installs a branching trigger by queuing a reapply for either the trigger
    /// concept (concept trigger) or the trigger role (role trigger).
    ///
    /// KONCLUDE-PORT-NOTE[api]: `CConceptRoleBranchingTrigger*` /
    /// `CProcessingRestrictionSpecification*` are not yet ported → opaque handles; the
    /// `isConceptTrigger`/`getTrigger*` discrimination is `W6-DEFER[api]`.
    pub fn install_concept_role_branch_trigger(
        &mut self,
        process_indi: &mut NodeId,
        concept_descriptor: ConDescId,
        dep_track_point: TrackPointId,
        proc_rest: ProcRestrictionHandle,
        trigger: BranchingTriggerHandle,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W6-DEFER[api]: is_concept_trigger = trigger->isConceptTrigger() — the trigger
        // type is an unported satellite; the branch is held as the concept-trigger arm
        // (the predominant case) with both arms transcribed in-comment.
        let is_concept_trigger = true;
        if is_concept_trigger {
            // W3-DEFER[macro]: STATINC(CONCEPTTRIGGERINSTALLCOUNT, calcAlgContext)
            // W6-DEFER[api]: triggerConcept = trigger->getTriggerConcept();
            //                triggerNegation = trigger->getTriggerNegation();
            let trigger_concept: ConceptId = Id::NONE;
            let trigger_negation = false;
            // addConceptToReapplyQueue(conceptDescriptor, triggerConcept, triggerNegation,
            //     processIndi, procRest, depTrackPoint, calcAlgContext)
            // — the CConcept* + negation + CProcessingRestrictionSpecification* overload (u10).
            self.add_concept_to_reapply_queue_concept_restricted(
                concept_descriptor,
                trigger_concept,
                trigger_negation,
                *process_indi,
                proc_rest,
                dep_track_point,
                calc_alg_context,
            );
        } else {
            // W3-DEFER[macro]: STATINC(ROLETRIGGERINSTALLCOUNT, calcAlgContext)
            // W6-DEFER[api]: role = trigger->getTriggerRole();
            let role: RoleId = Id::NONE;
            // addConceptToReapplyQueue(conceptDescriptor, role, processIndi, procRest,
            //     depTrackPoint, calcAlgContext)
            // — the CRole* + CProcessingRestrictionSpecification* overload (u10).
            self.add_concept_to_reapply_queue_role_restricted(
                concept_descriptor,
                role,
                *process_indi,
                proc_rest,
                dep_track_point,
                calc_alg_context,
            );
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::searchNextConceptRoleBranchTrigger`.
    /// cpp 17221-17240.
    ///
    /// Walks the trigger chain and returns the first trigger that is NOT yet satisfied
    /// on `process_indi` — a concept trigger whose concept is absent from the node's
    /// reapply concept-label set, or a role trigger whose role has no successor in the
    /// node's reapply role-successor hash.
    pub fn search_next_concept_role_branch_trigger(
        &mut self,
        process_indi: &mut NodeId,
        triggers: BranchingTriggerHandle,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> BranchingTriggerHandle {
        // reapplySuccHash = processIndi->getReapplyRoleSuccessorHash(false);
        // conSet = processIndi->getReapplyConceptLabelSet(false);
        // W6-DEFER[api]: getReapplyRoleSuccessorHash / getReapplyConceptLabelSet are
        //   unported node satellites; resolved as Id::NONE here.
        let reapply_succ_hash: Cint64 = INVALID;
        let con_set: LabelSetId = Id::NONE;
        let mut triggers = triggers;
        while triggers != INVALID {
            // W6-DEFER[api]: triggers->isConceptTrigger() (trigger satellite).
            let is_concept_trigger = true;
            if is_concept_trigger {
                // triggerConcept = triggers->getTriggerConcept();
                // triggerNegation = triggers->getTriggerNegation();
                let trigger_concept: ConceptId = Id::NONE;
                let trigger_negation = false;
                // if (!conSet || !conSet->containsConcept(triggerConcept, triggerNegation)): return triggers;
                // W6-DEFER[api]: CReapplyConceptLabelSet::containsConcept is not yet ported;
                //   the !conSet short-circuit is honoured (con_set == Id::NONE).
                let contains_concept = con_set != Id::NONE; // && conSet->containsConcept(...)
                if !contains_concept {
                    return triggers;
                }
                let _ = (trigger_concept, trigger_negation);
            } else {
                // role = triggers->getTriggerRole();
                let role: RoleId = Id::NONE;
                // if (!reapplySuccHash || !reapplySuccHash->hasRoleSuccessor(role)): return triggers;
                // W6-DEFER[api]: CReapplyRoleSuccessorHash::hasRoleSuccessor not yet ported.
                let has_role_successor = reapply_succ_hash != INVALID; // && reapplySuccHash->hasRoleSuccessor(role)
                if !has_role_successor {
                    return triggers;
                }
                let _ = role;
            }
            // triggers = triggers->getNextBranchingTrigger();
            // W6-DEFER[api]: trigger-chain advance — with the satellite unported the
            //   chain terminates (INVALID) so the walk is bounded.
            triggers = INVALID;
        }
        let _ = process_indi;
        INVALID
    }

    // =======================================================================
    // Successor-role link lookup (cpp 17307-17319).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::getIndividualNodeLink`.
    /// cpp 17307-17319.
    ///
    /// Returns the (first) link edge from `indi_source` to `indi_destination` carrying
    /// `role`, by scanning the source's successor-role iterator for the destination
    /// individual id and returning the first edge whose link-role matches.
    pub fn get_individual_node_link(
        &mut self,
        indi_source: &mut NodeId,
        indi_destination: &mut NodeId,
        role: RoleId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> EdgeId {
        // succRoleHash = indiSource->getSuccessorRoleHash(false);
        let succ_role_hash = calc_alg_context
            .process_context()
            .node(*indi_source)
            .use_succ_role_hash;
        if succ_role_hash.is_some() {
            let dest_indi_id = calc_alg_context
                .process_context()
                .node(*indi_destination)
                .individual_node_id();
            let mut succ_role_it = calc_alg_context
                .process_context()
                .node_successor_role_iterator(*indi_source, dest_indi_id);
            while succ_role_it.has_next() {
                let link = succ_role_it.next(true);
                if calc_alg_context
                    .process_context()
                    .edge(link)
                    .get_link_role()
                    == role
                {
                    return link;
                }
            }
        }
        Id::NONE
    }

    // =======================================================================
    // Label-concept set tests (cpp 17466, 17547, 17642).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::isLabelConceptSubSet`.
    /// cpp 17466-17543.
    ///
    /// Tests whether `sub_concept_set` ⊆ `super_concept_set` (by concept descriptor /
    /// concept tag + negation), optionally reporting the first not-entailed descriptor
    /// and whether the two sets are equal. The count fast-fails + the threshold-driven
    /// choice between a direct-lookup walk and a sorted tag-merge walk are ported
    /// faithfully over the live `CReapplyConceptLabelSetIterator`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: the nullable out-pointers
    /// `CConceptDescriptor** firstNotEntailedConDes` / `bool* equalConSet` become
    /// `Option<&mut ConDescId>` / `Option<&mut bool>`.
    pub fn is_label_concept_sub_set(
        &mut self,
        sub_concept_set: LabelSetId,
        super_concept_set: LabelSetId,
        first_not_entailed_con_des: Option<&mut ConDescId>,
        equal_con_set: Option<&mut bool>,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W3-DEFER[macro]: STATINC(LABELCONCEPTSUBSETTESTCOUNT, calcAlgContext)
        let mut first_not_entailed_con_des = first_not_entailed_con_des;
        let mut equal_con_set = equal_con_set;
        let sub_con_set_count = calc_alg_context
            .process_context()
            .label_set(sub_concept_set)
            .get_concept_count();
        let super_con_set_count = calc_alg_context
            .process_context()
            .label_set(super_concept_set)
            .get_concept_count();
        if let Some(out_eq) = equal_con_set.as_deref_mut() {
            if sub_con_set_count != super_con_set_count {
                *out_eq = false;
            } else {
                *out_eq = true;
            }
        }
        if sub_con_set_count > super_con_set_count {
            return false;
        }
        if super_con_set_count == 0 {
            return true;
        }
        let threshold_factor: Cint64 = 10;
        if sub_con_set_count * threshold_factor < super_con_set_count {
            let mut sub_con_set_it = calc_alg_context
                .process_context()
                .label_set_concept_label_set_iterator(sub_concept_set, true, false, false);
            while sub_con_set_it.has_value() {
                let sub_con_des = sub_con_set_it.get_concept_descriptor();
                let concept = calc_alg_context
                    .process_context()
                    .con_desc(sub_con_des)
                    .get_concept();
                let negated = calc_alg_context
                    .process_context()
                    .con_desc(sub_con_des)
                    .is_negated();
                if !self.label_set_contains_concept_resolved(
                    super_concept_set,
                    concept,
                    negated,
                    calc_alg_context,
                ) {
                    if let Some(out) = first_not_entailed_con_des.as_deref_mut() {
                        *out = sub_con_des;
                    }
                    return false;
                }
                sub_con_set_it.move_next(calc_alg_context.process_context());
            }
        } else {
            let mut sub_con_set_it = calc_alg_context
                .process_context()
                .label_set_concept_label_set_iterator(sub_concept_set, true, false, false);
            let mut super_con_set_it = calc_alg_context
                .process_context()
                .label_set_concept_label_set_iterator(super_concept_set, true, false, false);
            let mut super_con_des = super_con_set_it.get_concept_descriptor();
            let mut super_con_tag = super_con_set_it.get_data_tag(
                calc_alg_context.process_context(),
                calc_alg_context.ontology_arenas(),
            );
            super_con_set_it.move_next(calc_alg_context.process_context());
            while sub_con_set_it.has_value() {
                let sub_con_des = sub_con_set_it.get_concept_descriptor();
                let sub_con_tag = sub_con_set_it.get_data_tag(
                    calc_alg_context.process_context(),
                    calc_alg_context.ontology_arenas(),
                );
                while super_con_tag < sub_con_tag {
                    if !super_con_set_it.has_value() {
                        if let Some(out) = first_not_entailed_con_des.as_deref_mut() {
                            *out = sub_con_des;
                        }
                        return false;
                    }
                    super_con_des = super_con_set_it.get_concept_descriptor();
                    super_con_tag = super_con_set_it.get_data_tag(
                        calc_alg_context.process_context(),
                        calc_alg_context.ontology_arenas(),
                    );
                    super_con_set_it.move_next(calc_alg_context.process_context());
                    if super_con_tag < sub_con_tag {
                        if let Some(out_eq) = equal_con_set.as_deref_mut() {
                            *out_eq = false;
                        }
                    }
                }
                if sub_con_tag != super_con_tag {
                    if let Some(out) = first_not_entailed_con_des.as_deref_mut() {
                        *out = sub_con_des;
                    }
                    if let Some(out_eq) = equal_con_set.as_deref_mut() {
                        *out_eq = false;
                    }
                    return false;
                } else if calc_alg_context
                    .process_context()
                    .con_desc(sub_con_des)
                    .is_negated()
                    != calc_alg_context
                        .process_context()
                        .con_desc(super_con_des)
                        .is_negated()
                {
                    if let Some(out) = first_not_entailed_con_des.as_deref_mut() {
                        *out = sub_con_des;
                    }
                    if let Some(out_eq) = equal_con_set.as_deref_mut() {
                        *out_eq = false;
                    }
                    return false;
                }
                sub_con_set_it.move_next(calc_alg_context.process_context());
            }
        }
        true
    }

    fn are_label_concept_sets_equal_in_sorted_lockstep(
        concept_set1: LabelSetId,
        concept_set2: LabelSetId,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> bool {
        let mut con_set1_it = calc_alg_context
            .process_context()
            .label_set_concept_label_set_iterator(concept_set1, true, false, false);
        let mut con_set2_it = calc_alg_context
            .process_context()
            .label_set_concept_label_set_iterator(concept_set2, true, false, false);
        while con_set1_it.has_value() {
            if !con_set2_it.has_value() {
                return false;
            }
            let con_des1 = con_set1_it.get_concept_descriptor();
            let con_des2 = con_set2_it.get_concept_descriptor();
            if calc_alg_context
                .process_context()
                .con_desc(con_des1)
                .get_concept()
                != calc_alg_context
                    .process_context()
                    .con_desc(con_des2)
                    .get_concept()
            {
                return false;
            }
            if calc_alg_context
                .process_context()
                .con_desc(con_des1)
                .is_negated()
                != calc_alg_context
                    .process_context()
                    .con_desc(con_des2)
                    .is_negated()
            {
                return false;
            }
            con_set1_it.move_next(calc_alg_context.process_context());
            con_set2_it.move_next(calc_alg_context.process_context());
        }
        true
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::isLabelConceptEqualSet`.
    /// cpp 17547-17575.
    ///
    /// Set-equality of two concept-label sets: equal count, signature-equivalent,
    /// and (concept, negation)-identical in sorted lockstep.
    pub fn is_label_concept_equal_set(
        &mut self,
        concept_set1: LabelSetId,
        concept_set2: LabelSetId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W3-DEFER[macro]: STATINC(LABELCONCEPTEQUALSETTESTCOUNT, calcAlgContext)
        let concept_set1_count = calc_alg_context
            .process_context()
            .label_set(concept_set1)
            .get_concept_count();
        let concept_set2_count = calc_alg_context
            .process_context()
            .label_set(concept_set2)
            .get_concept_count();
        if concept_set1_count != concept_set2_count {
            return false;
        }
        if !calc_alg_context
            .process_context()
            .label_set(concept_set1)
            .concept_signature
            .is_signature_equivalent(
                &calc_alg_context
                    .process_context()
                    .label_set(concept_set2)
                    .concept_signature,
            )
        {
            return false;
        }
        Self::are_label_concept_sets_equal_in_sorted_lockstep(
            concept_set1,
            concept_set2,
            calc_alg_context,
        )
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::isPairwiseLabelConceptEqualSet`.
    /// cpp 17642-17695.
    ///
    /// Pairwise set-equality used by pairwise-equal-set blocking: each of the two
    /// (set, pair-set) couples must agree in count, be signature-equivalent, and be
    /// (concept, negation)-identical in sorted lockstep.
    pub fn is_pairwise_label_concept_equal_set(
        &mut self,
        concept_set1: LabelSetId,
        concept_set1_pair: LabelSetId,
        concept_set2: LabelSetId,
        concept_set2_pair: LabelSetId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W3-DEFER[macro]: STATINC(LABELCONCEPTPAIRWISEEQUALSETTESTCOUNT, calcAlgContext)
        let concept_set1_count = calc_alg_context
            .process_context()
            .label_set(concept_set1)
            .get_concept_count();
        let concept_set1p_count = calc_alg_context
            .process_context()
            .label_set(concept_set1_pair)
            .get_concept_count();
        if concept_set1_count != concept_set1p_count {
            return false;
        }
        let concept_set2_count = calc_alg_context
            .process_context()
            .label_set(concept_set2)
            .get_concept_count();
        let concept_set2p_count = calc_alg_context
            .process_context()
            .label_set(concept_set2_pair)
            .get_concept_count();
        if concept_set2_count != concept_set2p_count {
            return false;
        }
        if !calc_alg_context
            .process_context()
            .label_set(concept_set1)
            .concept_signature
            .is_signature_equivalent(
                &calc_alg_context
                    .process_context()
                    .label_set(concept_set1_pair)
                    .concept_signature,
            )
        {
            return false;
        }
        if !calc_alg_context
            .process_context()
            .label_set(concept_set2)
            .concept_signature
            .is_signature_equivalent(
                &calc_alg_context
                    .process_context()
                    .label_set(concept_set2_pair)
                    .concept_signature,
            )
        {
            return false;
        }
        if !Self::are_label_concept_sets_equal_in_sorted_lockstep(
            concept_set1,
            concept_set1_pair,
            calc_alg_context,
        ) {
            return false;
        }
        Self::are_label_concept_sets_equal_in_sorted_lockstep(
            concept_set2,
            concept_set2_pair,
            calc_alg_context,
        )
    }

    // =======================================================================
    // Variable-propagation-binding association-concept collection (cpp 18055-18149).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::collectIndividualNodeVariablePropagationBindings`.
    /// cpp 18055-18084.
    ///
    /// Collects every live variable-binding path on `individual_node` (keyed by its
    /// propagation id) into `collecting_propagation_variable_bindings_hash`; returns
    /// whether any were found.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: the collecting `QHash<cint64, CVariableBindingPath*>`
    /// becomes a `&mut Vec<(Cint64, VarBindingPathId)>`; inserting an existing key
    /// replaces the stored path, matching `QHash::insert`.
    pub fn collect_individual_node_variable_propagation_bindings(
        &mut self,
        individual_node: &mut NodeId,
        collecting_propagation_variable_bindings_hash: &mut Vec<(
            Cint64,
            VariableBindingPathHandle,
        )>,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let collected_paths: Vec<(Cint64, VarBindingPathId)> = {
            let pc = calc_alg_context.process_context();
            let con_var_bind_set_hash =
                pc.node(*individual_node).use_concept_var_bind_path_set_hash;
            if con_var_bind_set_hash.is_none() {
                return false;
            }

            let mut collected_paths = Vec::new();
            for hash_data in pc
                .con_var_bind_path_set_hash(con_var_bind_set_hash)
                .map
                .values()
            {
                let var_bind_set = hash_data.use_variable_binding_path_set;
                if var_bind_set.is_none() {
                    continue;
                }
                let con_des = pc.vbpath_set(var_bind_set).get_concept_descriptor();
                if con_des.is_none() {
                    continue;
                }

                for map_data in pc
                    .vbpath_set(var_bind_set)
                    .get_variable_binding_path_map()
                    .map
                    .values()
                {
                    let var_bind_des = map_data.get_variable_binding_path_descriptor();
                    if var_bind_des.is_some() {
                        let var_bind_path = pc.vbpath_des(var_bind_des).get_variable_binding_path();
                        if var_bind_path.is_some() {
                            collected_paths.push((
                                pc.vbpath(var_bind_path).get_propagation_id(),
                                var_bind_path,
                            ));
                        }
                    }
                }
            }
            collected_paths
        };

        let found_var_prop_bindings = !collected_paths.is_empty();
        for (propagation_id, var_bind_path) in collected_paths {
            if let Some((_existing_prop_id, existing_path)) =
                collecting_propagation_variable_bindings_hash
                    .iter_mut()
                    .find(|(prop_id, _)| *prop_id == propagation_id)
            {
                *existing_path = var_bind_path;
            } else {
                collecting_propagation_variable_bindings_hash.push((propagation_id, var_bind_path));
            }
        }
        found_var_prop_bindings
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::getIndividualNodeAssociatedConceptsSetFromVariablePropagationBindings`.
    /// cpp 18102-18114.
    ///
    /// For each variable-binding path on `individual_node`, gathers the concept set
    /// the path is compatible with, returning the SET of those concept sets.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: `QSet<QSet<CConcept*>>` becomes
    /// `Vec<Vec<ConceptId>>` (set-of-sets, insertion-ordered — the inner `Vec` is not
    /// `Hash`, see `IndiAssociatedConceptSetCacheData`).
    pub fn get_individual_node_associated_concepts_set_from_variable_propagation_bindings(
        &mut self,
        individual_node: &mut NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> Vec<Vec<ConceptId>> {
        let mut associated_concepts_set: Vec<Vec<ConceptId>> = Vec::new();

        let mut variable_propagation_binding_collection_hash: Vec<(
            Cint64,
            VariableBindingPathHandle,
        )> = Vec::new();
        self.collect_individual_node_variable_propagation_bindings(
            individual_node,
            &mut variable_propagation_binding_collection_hash,
            calc_alg_context,
        );

        for &(_prop_id, var_bind_path) in variable_propagation_binding_collection_hash.iter() {
            // associatedConceptSet = getConceptsForCompatibleVariablePropagationBindings(individualNode, varBindPath, ctx)
            let associated_concept_set = self
                .get_concepts_for_compatible_variable_propagation_bindings(
                    individual_node,
                    var_bind_path,
                    calc_alg_context,
                );
            // associatedConceptsSet.insert(associatedConceptSet) — QSet de-dups; mirror with contains-guard.
            if !associated_concepts_set.contains(&associated_concept_set) {
                associated_concepts_set.push(associated_concept_set);
            }
        }
        associated_concepts_set
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::getIndividualNodesListAssociatedConceptsSetFromVariablePropagationBindings`.
    /// cpp 18120-18149.
    ///
    /// The multi-node variant: over the union of `individual_node`'s and
    /// `ancestor_individual_node`'s variable-binding paths, builds — per path — the
    /// LIST of compatible concept sets across (test node, ancestor node, each
    /// dependent nominal), returning the SET of those lists.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: `QSet<QList<QSet<CConcept*>>>` →
    /// `Vec<Vec<Vec<ConceptId>>>` (set-of-lists-of-sets, insertion-ordered, de-duped).
    pub fn get_individual_nodes_list_associated_concepts_set_from_variable_propagation_bindings(
        &mut self,
        individual_node: &mut NodeId,
        ancestor_individual_node: &mut NodeId,
        dependent_nominal_id_list: &[Cint64],
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> Vec<Vec<Vec<ConceptId>>> {
        let mut variable_propagation_binding_collection_hash: Vec<(
            Cint64,
            VariableBindingPathHandle,
        )> = Vec::new();
        self.collect_individual_node_variable_propagation_bindings(
            individual_node,
            &mut variable_propagation_binding_collection_hash,
            calc_alg_context,
        );
        self.collect_individual_node_variable_propagation_bindings(
            ancestor_individual_node,
            &mut variable_propagation_binding_collection_hash,
            calc_alg_context,
        );
        // (No need to collect from the nominal nodes — identical for blocker + blocked.)

        let mut all_variable_mappings_associated_concepts_over_nodes_list_set: Vec<
            Vec<Vec<ConceptId>>,
        > = Vec::new();

        for &(_prop_id, var_bind_path) in variable_propagation_binding_collection_hash.iter() {
            let mut associated_concepts_over_nodes_list: Vec<Vec<ConceptId>> = Vec::new();
            let test_indi_associated_concept_set = self
                .get_concepts_for_compatible_variable_propagation_bindings(
                    individual_node,
                    var_bind_path,
                    calc_alg_context,
                );
            associated_concepts_over_nodes_list.push(test_indi_associated_concept_set);
            let ancestor_test_indi_associated_concept_set = self
                .get_concepts_for_compatible_variable_propagation_bindings(
                    ancestor_individual_node,
                    var_bind_path,
                    calc_alg_context,
                );
            associated_concepts_over_nodes_list.push(ancestor_test_indi_associated_concept_set);

            for &nom_indi_id in dependent_nominal_id_list.iter() {
                // nominalIndiNode = getCorrectedNominalIndividualNode(nomIndiId, ctx)
                let mut nominal_indi_node =
                    self.get_corrected_nominal_individual_node(nom_indi_id, calc_alg_context);
                let nominal_indi_associated_concept_set = self
                    .get_concepts_for_compatible_variable_propagation_bindings(
                        &mut nominal_indi_node,
                        var_bind_path,
                        calc_alg_context,
                    );
                associated_concepts_over_nodes_list.push(nominal_indi_associated_concept_set);
            }

            // QSet de-dups the resulting list; mirror with contains-guard.
            if !all_variable_mappings_associated_concepts_over_nodes_list_set
                .contains(&associated_concepts_over_nodes_list)
            {
                all_variable_mappings_associated_concepts_over_nodes_list_set
                    .push(associated_concepts_over_nodes_list);
            }
        }
        all_variable_mappings_associated_concepts_over_nodes_list_set
    }

    // =======================================================================
    // Anonymous variable-propagation analogous-path blocking (cpp 18155-18383).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::isAnonymousVariablePropagationBindingSingleIndividualAnalogousPath`.
    /// cpp 18155-18258.
    ///
    /// The single-node analogous-path test: caches each node's
    /// associated-concept-set-set (keyed by its last propagated variable-binding
    /// descriptor) on a `CBlockingVariableBindingsAnalogousPropagationData` satellite,
    /// short-circuits on a cheap concept-set hash-value difference, and finally
    /// compares the two associated-concept-set-sets for set-equality.
    pub fn is_anonymous_variable_propagation_binding_single_individual_analogous_path(
        &mut self,
        test_indi: &mut NodeId,
        blocking_indi: &mut NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // PORT-PENDING: faithful transcription of cpp 18155-18258. The body hangs on
        // two not-yet-ported node satellites and one variable-binding accessor:
        //   * CBlockingVariableBindingsAnalogousPropagationData (VarPropBlockDataId) —
        //     getVariableBindingsPropagationBlockingData / set..., with
        //     get/setLastConceptSetsHashValue + get/setLastPropagatedVariableBindingDescriptor;
        //   * CConceptVariableBindingPathSetHash (ConceptVarBindPathSetHashId) —
        //     getConceptVariableBindingPathSetHash + getLastVariableBindingDescriptionLinker;
        //   * the cached set builder getIndividualNodeAssociatedConceptsSetFromVariablePropagationBindings(Cached)
        //     (this unit, non-cached variant ported above) + getBindingsCompatibleConceptSetsHashValue (sibling).
        //
        // Faithful control flow:
        //   testVarBindBlockData     = testIndi->getVariableBindingsPropagationBlockingData(false);
        //   blockingVarBindBlockData = blockingIndi->getVariableBindingsPropagationBlockingData(false);
        //   testConVarBindPathSetHash     = testIndi->getConceptVariableBindingPathSetHash(false);
        //   blockingConVarBindPathSetHash = blockingIndi->getConceptVariableBindingPathSetHash(false);
        //   // cheap up-to-date hash-value short-circuit:
        //   if testVarBindBlockData && blockingVarBindBlockData
        //      && testConVarBindPathSetHash && testVarBindBlockData->getLastPropagatedVariableBindingDescriptor()
        //                                       == testConVarBindPathSetHash->getLastVariableBindingDescriptionLinker()
        //      && blockingConVarBindPathSetHash && blockingVarBindBlockData->getLastPropagatedVariableBindingDescriptor()
        //                                       == blockingConVarBindPathSetHash->getLastVariableBindingDescriptionLinker()
        //      && testVarBindBlockData->getLastConceptSetsHashValue() != blockingVarBindBlockData->getLastConceptSetsHashValue():
        //         STATINC(SIMPLEANALOGOUSPROPAGATIONBLOCKINGCONCEPTSETHASHVALUEDIFFERENCECOUNT, ctx); return false;
        //   // (re)build + cache the test side if its descriptor moved:
        //   if !testVarBindBlockData: alloc CBlockingVariableBindingsAnalogousPropagationData; setVariableBindingsPropagationBlockingData
        //   if testConVarBindPathSetHash && testVarBindBlockData->getLastPropagatedVariableBindingDescriptor()
        //        != testConVarBindPathSetHash->getLastVariableBindingDescriptionLinker():
        //     testIndiAssociatedConceptSetSet = getIndividualNodeAssociatedConceptsSetFromVariablePropagationBindingsCached(testIndi, ctx);
        //     testConceptSetsHashValue = getBindingsCompatibleConceptSetsHashValue(testIndiAssociatedConceptSetSet, ctx);
        //     testVarBindBlockData = testIndi->getVariableBindingsPropagationBlockingData(true) (alloc if null);
        //     testVarBindBlockData->setLastConceptSetsHashValue(testConceptSetsHashValue);
        //     testVarBindBlockData->setLastPropagatedVariableBindingDescriptor(testConVarBindPathSetHash->getLastVariableBindingDescriptionLinker());
        //   // symmetric (re)build + cache for the blocking side;
        //   if testVarBindBlockData->getLastConceptSetsHashValue() != blockingVarBindBlockData->getLastConceptSetsHashValue():
        //       STATINC(...HASHVALUEDIFFERENCECOUNT, ctx); return false;
        //   if !testIndiAssociatedConceptSetSetCreated:     testIndiAssociatedConceptSetSet = ...Cached(testIndi, ctx);
        //   if !blockingIndiAssociatedConceptSetSetCreated: blockingIndiAssociatedConceptSetSet = ...(blockingIndi, ctx);
        //   // (debug-only KONCLUCE_..._INSTRUCTION block writing the associated-concepts strings — dropped: debug)
        //   if testIndiAssociatedConceptSetSet != blockingIndiAssociatedConceptSetSet: return false;
        //   return true;
        //
        // Held PORT-PENDING because the cache satellite + the path-set-hash + the
        // cached set-builder + getBindingsCompatibleConceptSetsHashValue are all
        // unported; the non-cached set builder above gives the later wave its anchor.
        let _ = (test_indi, blocking_indi, calc_alg_context);
        true
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::isAnonymousVariablePropagationBindingAnalogousPath`.
    /// cpp 18283-18383.
    ///
    /// The full analogous-path blocking test: requires the single-node analogous test
    /// to hold for both (test, blocking) and their ancestors, then (over the union of
    /// the involved dependent nominals) requires the multi-node associated-concept-set
    /// lists to be set-equal.
    ///
    /// KONCLUDE-PORT-NOTE[api]: the C++ `blockData` / `testContinueBlocking` /
    /// `blockAltData` parameters are blocking-test satellites not yet ported; they are
    /// carried as opaque handles (the body does not branch on them — they reach the
    /// debug-only paths only).
    pub fn is_anonymous_variable_propagation_binding_analogous_path(
        &mut self,
        test_indi: &mut NodeId,
        blocking_indi: &mut NodeId,
        block_data: IndiBlockDataId,
        test_continue_blocking: bool,
        block_alt_data: BlockingTestDataHandle,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // (Leading KONCLUCE_..._INSTRUCTION debug-write block + mFirstBlockingTestDebugWritten
        //  one-shot debug dump — debug-only, dropped.)

        // W3-DEFER[macro]: STATINC(SIMPLEANALOGOUSPROPAGATIONBLOCKINGTESTCOUNT, calcAlgContext)
        if !self.is_anonymous_variable_propagation_binding_single_individual_analogous_path(
            test_indi,
            blocking_indi,
            calc_alg_context,
        ) {
            // W3-DEFER[macro]: STATINC(SIMPLEANALOGOUSPROPAGATIONBLOCKINGFAILCOUNT, calcAlgContext)
            return false;
        }

        // ancestorIndiNode    = getAncestorIndividual(testIndi, ctx);
        // ancestorBlockingIndi = getAncestorIndividual(blockingIndi, ctx);
        let mut ancestor_indi_node = self.get_ancestor_individual(test_indi, calc_alg_context);
        let mut ancestor_blocking_indi =
            self.get_ancestor_individual(blocking_indi, calc_alg_context);
        if !self.is_anonymous_variable_propagation_binding_single_individual_analogous_path(
            &mut ancestor_indi_node,
            &mut ancestor_blocking_indi,
            calc_alg_context,
        ) {
            // W3-DEFER[macro]: STATINC(SIMPLEANALOGOUSPROPAGATIONBLOCKINGFAILCOUNT, calcAlgContext)
            return false;
        }

        // W3-DEFER[macro]: STATINC(SIMPLEANALOGOUSPROPAGATIONBLOCKINGSUCCESSCOUNT, calcAlgContext)

        // First: determine the ordered list of dependent (nominal) nodes — the union
        // of testIndi's and blockingIndi's successor-connected-nominal sets (blocking
        // side adds only the ids the test side lacks).
        let mut dependent_nominal_id_list: Vec<Cint64> = Vec::new();
        // testIndiSuccConnNomSet = testIndi->getSuccessorNominalConnectionSet(false);
        // blockingIndiSuccConnNomSet = blockingIndi->getSuccessorNominalConnectionSet(false);
        // W6-DEFER[api]: getSuccessorNominalConnectionSet is an unported node satellite
        //   (NominalConnectionSetId); with both sets unresolved the dependent-nominal
        //   list stays empty (faithful for the nominal-free case). Logic:
        //     for it in testIndiSuccConnNomSet: dependentNominalIdList.append(*it);
        //     for it in blockingIndiSuccConnNomSet:
        //       if !testIndiSuccConnNomSet || !testIndiSuccConnNomSet->contains(*it):
        //         dependentNominalIdList.append(*it);
        // (The C++ `!dependentNominalIdList.isDetached()` STATINC is a Qt-COW probe — dropped.)

        // W3-DEFER[macro]: STATINC(FULLANALOGOUSPROPAGATIONBLOCKINGTESTCOUNT, calcAlgContext)
        // Second: get associated-concept-set lists over these nodes for both sides.
        let test_indi_all = self
            .get_individual_nodes_list_associated_concepts_set_from_variable_propagation_bindings(
                test_indi,
                &mut ancestor_indi_node,
                &dependent_nominal_id_list,
                calc_alg_context,
            );
        let blocking_indi_all = self
            .get_individual_nodes_list_associated_concepts_set_from_variable_propagation_bindings(
                blocking_indi,
                &mut ancestor_blocking_indi,
                &dependent_nominal_id_list,
                calc_alg_context,
            );

        // (KONCLUCE_..._INSTRUCTION debug-write of the over-nominals associated-concepts
        //  strings — debug-only, dropped.)

        // Third: compare (QSet equality is order-insensitive; both built de-duped here).
        if !self.associated_concepts_over_nodes_list_set_eq(&test_indi_all, &blocking_indi_all) {
            // W3-DEFER[macro]: STATINC(FULLANALOGOUSPROPAGATIONBLOCKINGFAILCOUNT, calcAlgContext)
            return false;
        }

        // W3-DEFER[macro]: STATINC(FULLANALOGOUSPROPAGATIONBLOCKINGSUCCESSCOUNT, calcAlgContext)
        let _ = (
            block_data,
            test_continue_blocking,
            block_alt_data,
            &mut dependent_nominal_id_list,
        );
        true
    }

    /// Order-insensitive equality of two set-of-lists-of-sets, mirroring the C++
    /// `QSet<QList<QSet<CConcept*>>>::operator!=` used by the analogous-path compare.
    /// Both operands are de-duped on construction (the `contains`-guarded pushes
    /// above), so set equality reduces to mutual containment.
    fn associated_concepts_over_nodes_list_set_eq(
        &self,
        a: &[Vec<Vec<ConceptId>>],
        b: &[Vec<Vec<ConceptId>>],
    ) -> bool {
        if a.len() != b.len() {
            return false;
        }
        for x in a.iter() {
            if !b.contains(x) {
                return false;
            }
        }
        true
    }
}
