//! `process::pn2` — method-batch unit **PN-2** of `CIndividualProcessNode`:
//! assertion / init-concept linker accessors + init-state flags + identity
//! (`Source/Reasoner/Kernel/Process/CIndividualProcessNode.cpp` lines 486–836).
//!
//! These are the (mostly trivial) get/set/has/clear/add accessors over the
//! node's processing-block test individual, the two initialising-concept linker
//! chains, the assertion concept/data/role/reverse-role linker chains, the
//! asserted-data-literal and additional-assertion linker chains, the
//! assertion-initialisation bool flags, and the identity scalars. They are ported
//! one-for-one with the C++ control flow; only the linker representation differs
//! (see notes below).
//!
//! KONCLUDE-PORT-NOTE[ownership]: the two initialising-concept linkers
//! (`mInitializingConceptLinkerIt`, `mProcessInitializingConceptLinkerIt`) are
//! modelled in `node.rs` as owned `Vec<NegLink<ConceptId>>` (per `substrate.rs`).
//! C++ holds a `CXSortedNegLinker<CConcept*>*` head pointer; a pointer copy shared
//! the chain, the port `.clone()`s / moves the `Vec`. `nullptr` == an empty `Vec`;
//! `head->append(tail)` (prepend-new, return-new-head) becomes `Vec::append`
//! (move `tail` onto the end of `new`). Iteration order is preserved.
//!
//! KONCLUDE-PORT-NOTE[ownership]: the asserted-data-literal and additional
//! assertion linker chains use concrete `CLinkerBase`-style records in
//! `process::stubs` plus per-test arenas on `ProcessContext`. Their `add*`
//! methods therefore take the ambient context so the incoming linker can be
//! prepended with `next = old_head`, matching C++ `linker->append(oldHead)`.
//!
//! SKIPPED (already ported elsewhere, NOT re-defined here to avoid duplicate
//! inherent methods):
//!   * `getIndividualNodeID` / `setIndividualNodeID` (`.cpp` 816/820) and
//!     `getIndividualType` / `setIndividualType` (`.cpp` 828/833) live in
//!     `node.rs` (`individual_node_id`/`set_individual_node_id`/`individual_type`/
//!     `set_individual_type`).
//!     KONCLUDE-PORT-NOTE[unclear]: `node.rs::set_individual_node_id` is a
//!     SIMPLIFIED placeholder — the faithful C++ `setIndividualNodeID` guards
//!     `if (mMergeIntoID == mIndiID) mMergeIntoID = indiID;` BEFORE `mIndiID = indiID;`
//!     which the `node.rs` version omits. Reconcile `node.rs` to the C++ body when
//!     the merge path lands; PN-2 cannot redefine the inherent method.

#![allow(dead_code)]

use super::super::model::individual::{
    ConceptAssertion, DataAssertion, ReverseRoleAssertion, RoleAssertion,
};
use super::super::model::{Cint64, ConceptId, NegLink};
use super::context::ProcessContext;
use super::node::IndividualProcessNode;
use super::stubs::{
    AdditionalDataAssertionsLinkerId, AdditionalRoleAssertionsLinkerId, ConceptAssertionLinkerId,
    DataAssertionLinkerId, ProcessAssertedDataLiteralLinkerId, ReverseRoleAssertionLinkerId,
    RoleAssertionLinkerId,
};
use super::NodeId;

impl IndividualProcessNode {
    // ===================================================================
    // Processing-block test individual.
    // ===================================================================

    /// Port of `CIndividualProcessNode::getProcessingBlockTestIndividual`.
    pub fn processing_block_test_individual(&self) -> NodeId {
        self.processing_blocked_indi
    }

    /// Port of `CIndividualProcessNode::clearProcessingBlockTestIndividual`.
    pub fn clear_processing_block_test_individual(&mut self) -> &mut Self {
        self.processing_blocked_indi = NodeId::NONE;
        self
    }

    /// Port of `CIndividualProcessNode::setProcessingBlockTestIndividual`.
    pub fn set_processing_block_test_individual(
        &mut self,
        processing_block_test_indi: NodeId,
    ) -> &mut Self {
        self.processing_blocked_indi = processing_block_test_indi;
        self
    }

    // ===================================================================
    // Initialising-concept linkers (Vec<NegLink<ConceptId>>; see module note).
    // ===================================================================

    /// Port of `CIndividualProcessNode::hasInitializingConcepts`.
    pub fn has_initializing_concepts(&self) -> bool {
        // mInitializingConceptLinkerIt != nullptr
        !self.initializing_concept_linker.is_empty()
    }

    /// Port of `CIndividualProcessNode::clearProcessInitializingConcepts`.
    pub fn clear_process_initializing_concepts(&mut self) -> &mut Self {
        // mProcessInitializingConceptLinkerIt = nullptr
        self.process_initializing_concept_linker.clear();
        self
    }

    /// Port of `CIndividualProcessNode::getProcessInitializingConceptLinker`.
    pub fn process_initializing_concept_linker(&self) -> &[NegLink<ConceptId>] {
        &self.process_initializing_concept_linker
    }

    /// Port of `CIndividualProcessNode::getInitializingConceptLinker`.
    pub fn initializing_concept_linker(&self) -> &[NegLink<ConceptId>] {
        &self.initializing_concept_linker
    }

    /// Port of `CIndividualProcessNode::setInitializingConceptLinker`.
    pub fn set_initializing_concept_linker(
        &mut self,
        initializing_concept_linker: Vec<NegLink<ConceptId>>,
    ) -> &mut Self {
        self.initializing_concept_linker = initializing_concept_linker;
        self
    }

    /// Port of `CIndividualProcessNode::addInitializingConceptLinker`.
    ///
    /// [ownership]: C++ `initializingConceptLinkerIt->append(mInitializingConceptLinkerIt)`
    /// prepends the new chain ahead of the existing head and returns the new head;
    /// the `Vec` port moves the existing entries onto the tail of the new chain.
    pub fn add_initializing_concept_linker(
        &mut self,
        mut initializing_concept_linker: Vec<NegLink<ConceptId>>,
    ) -> &mut Self {
        if !initializing_concept_linker.is_empty() {
            initializing_concept_linker.append(&mut self.initializing_concept_linker);
            self.initializing_concept_linker = initializing_concept_linker;
            self.process_initializing_concept_linker = self.initializing_concept_linker.clone();
        }
        self
    }

    // ===================================================================
    // Assertion concepts.
    // ===================================================================

    /// Port of `CIndividualProcessNode::hasAssertionConcepts`.
    pub fn has_assertion_concepts(&self) -> bool {
        self.assertion_concept_linker.is_some()
    }

    /// Port of `CIndividualProcessNode::clearAssertionConcepts`.
    pub fn clear_assertion_concepts(&mut self) -> &mut Self {
        self.assertion_concept_linker = ConceptAssertionLinkerId::NONE;
        self
    }

    /// Port of `CIndividualProcessNode::getAssertionConceptLinker`.
    pub fn assertion_concept_linker(&self) -> ConceptAssertionLinkerId {
        self.assertion_concept_linker
    }

    /// Port of `CIndividualProcessNode::setAssertionConceptLinker`.
    pub fn set_assertion_concept_linker(
        &mut self,
        assertion_concept_linker: ConceptAssertionLinkerId,
    ) -> &mut Self {
        self.assertion_concept_linker = assertion_concept_linker;
        self
    }

    /// Rust-owned bridge for `setAssertionConceptLinker`.
    pub fn assertion_concept_assertions(&self) -> &[ConceptAssertion] {
        &self.assertion_concept_assertions
    }

    /// Replace the value-backed assertion concept chain.
    pub fn set_assertion_concept_assertions(
        &mut self,
        assertion_concepts: Vec<ConceptAssertion>,
    ) -> &mut Self {
        self.assertion_concept_assertions = assertion_concepts;
        self
    }

    // ===================================================================
    // Assertion data.
    // ===================================================================

    /// Port of `CIndividualProcessNode::hasAssertionData`.
    pub fn has_assertion_data(&self) -> bool {
        self.assertion_data_linker.is_some()
    }

    /// Port of `CIndividualProcessNode::clearAssertionData`.
    pub fn clear_assertion_data(&mut self) -> &mut Self {
        self.assertion_data_linker = DataAssertionLinkerId::NONE;
        self
    }

    /// Port of `CIndividualProcessNode::getAssertionDataLinker`.
    pub fn assertion_data_linker(&self) -> DataAssertionLinkerId {
        self.assertion_data_linker
    }

    /// Port of `CIndividualProcessNode::setAssertionDataLinker`.
    pub fn set_assertion_data_linker(
        &mut self,
        assertion_data_linker: DataAssertionLinkerId,
    ) -> &mut Self {
        self.assertion_data_linker = assertion_data_linker;
        self
    }

    /// Rust-owned bridge for `setAssertionDataLinker`.
    pub fn assertion_data_assertions(&self) -> &[DataAssertion] {
        &self.assertion_data_assertions
    }

    /// Replace the value-backed assertion data chain.
    pub fn set_assertion_data_assertions(
        &mut self,
        assertion_data: Vec<DataAssertion>,
    ) -> &mut Self {
        self.assertion_data_assertions = assertion_data;
        self
    }

    // ===================================================================
    // Asserted data literals.
    // ===================================================================

    /// Port of `CIndividualProcessNode::hasAssertedDataLiterals`.
    pub fn has_asserted_data_literals(&self) -> bool {
        self.asserted_data_literal_linker.is_some()
    }

    /// Port of `CIndividualProcessNode::getAssertedDataLiteralLinker`.
    pub fn asserted_data_literal_linker(&self) -> ProcessAssertedDataLiteralLinkerId {
        self.asserted_data_literal_linker
    }

    /// Port of `CIndividualProcessNode::setAssertedDataLiteralLinker`.
    pub fn set_asserted_data_literal_linker(
        &mut self,
        data_literal_linker: ProcessAssertedDataLiteralLinkerId,
    ) -> &mut Self {
        self.asserted_data_literal_linker = data_literal_linker;
        self
    }

    /// Port of `CIndividualProcessNode::getLastProcessedAssertionDataLinker`.
    pub fn last_processed_assertion_data_linker(&self) -> DataAssertionLinkerId {
        self.last_processed_assertion_data_linker
    }

    /// Port of `CIndividualProcessNode::setLastProcessedAssertionDataLinker`.
    pub fn set_last_processed_assertion_data_linker(
        &mut self,
        data_literal_linker: DataAssertionLinkerId,
    ) -> &mut Self {
        self.last_processed_assertion_data_linker = data_literal_linker;
        self
    }

    /// Port of `CIndividualProcessNode::getLastAssertedDataLiteralLinker`.
    pub fn last_asserted_data_literal_linker(&self) -> ProcessAssertedDataLiteralLinkerId {
        self.last_asserted_data_literal_linker
    }

    /// Port of `CIndividualProcessNode::setLastAssertedDataLiteralLinker`.
    pub fn set_last_asserted_data_literal_linker(
        &mut self,
        data_literal_linker: ProcessAssertedDataLiteralLinkerId,
    ) -> &mut Self {
        self.last_asserted_data_literal_linker = data_literal_linker;
        self
    }

    /// Port of `CIndividualProcessNode::addAssertedDataLiteralLinker`.
    pub fn add_asserted_data_literal_linker(
        &mut self,
        data_literal_linker: ProcessAssertedDataLiteralLinkerId,
        process_context: &mut ProcessContext,
    ) -> &mut Self {
        // mAssertedDataLiteralLinker = dataLiteralLinker->append(mAssertedDataLiteralLinker);
        if data_literal_linker.is_some() {
            process_context
                .process_asserted_data_literal_linker_mut(data_literal_linker)
                .set_next(self.asserted_data_literal_linker);
        }
        self.asserted_data_literal_linker = data_literal_linker;
        self
    }

    /// Port of `CIndividualProcessNode::clearAssertedDataLiterals`.
    pub fn clear_asserted_data_literals(&mut self) -> &mut Self {
        self.asserted_data_literal_linker = ProcessAssertedDataLiteralLinkerId::NONE;
        self
    }

    // ===================================================================
    // Assertion roles.
    // ===================================================================

    /// Port of `CIndividualProcessNode::hasAssertionRoles`.
    pub fn has_assertion_roles(&self) -> bool {
        self.assertion_role_linker.is_some()
    }

    /// Port of `CIndividualProcessNode::clearAssertionRoles`.
    pub fn clear_assertion_roles(&mut self) -> &mut Self {
        self.assertion_role_linker = RoleAssertionLinkerId::NONE;
        self
    }

    /// Port of `CIndividualProcessNode::getAssertionRoleLinker`.
    pub fn assertion_role_linker(&self) -> RoleAssertionLinkerId {
        self.assertion_role_linker
    }

    /// Port of `CIndividualProcessNode::setAssertionRoleLinker`.
    pub fn set_assertion_role_linker(
        &mut self,
        assertion_role_linker: RoleAssertionLinkerId,
    ) -> &mut Self {
        self.assertion_role_linker = assertion_role_linker;
        self
    }

    /// Rust-owned bridge for `setAssertionRoleLinker`.
    pub fn assertion_role_assertions(&self) -> &[RoleAssertion] {
        &self.assertion_role_assertions
    }

    /// Replace the value-backed assertion role chain.
    pub fn set_assertion_role_assertions(
        &mut self,
        assertion_roles: Vec<RoleAssertion>,
    ) -> &mut Self {
        self.assertion_role_assertions = assertion_roles;
        self
    }

    /// Port of `CIndividualProcessNode::getRoleAssertionCreationID`.
    pub fn role_assertion_creation_id(&self) -> Cint64 {
        self.role_assertion_creation_id
    }

    /// Port of `CIndividualProcessNode::setRoleAssertionCreationID`.
    pub fn set_role_assertion_creation_id(&mut self, creation_id: Cint64) -> &mut Self {
        self.role_assertion_creation_id = creation_id;
        self
    }

    // ===================================================================
    // Reverse assertion roles.
    // ===================================================================

    /// Port of `CIndividualProcessNode::hasReverseAssertionRoles`.
    pub fn has_reverse_assertion_roles(&self) -> bool {
        self.reverse_assertion_role_linker.is_some()
    }

    /// Port of `CIndividualProcessNode::clearReverseAssertionRoles`.
    pub fn clear_reverse_assertion_roles(&mut self) -> &mut Self {
        self.reverse_assertion_role_linker = ReverseRoleAssertionLinkerId::NONE;
        self
    }

    /// Port of `CIndividualProcessNode::getReverseAssertionRoleLinker`.
    pub fn reverse_assertion_role_linker(&self) -> ReverseRoleAssertionLinkerId {
        self.reverse_assertion_role_linker
    }

    /// Port of `CIndividualProcessNode::setReverseAssertionRoleLinker`.
    pub fn set_reverse_assertion_role_linker(
        &mut self,
        reverse_assertion_role_linker: ReverseRoleAssertionLinkerId,
    ) -> &mut Self {
        self.reverse_assertion_role_linker = reverse_assertion_role_linker;
        self
    }

    /// Rust-owned bridge for `setReverseAssertionRoleLinker`.
    pub fn reverse_assertion_role_assertions(&self) -> &[ReverseRoleAssertion] {
        &self.reverse_assertion_role_assertions
    }

    /// Replace the value-backed reverse assertion role chain.
    pub fn set_reverse_assertion_role_assertions(
        &mut self,
        reverse_assertion_roles: Vec<ReverseRoleAssertion>,
    ) -> &mut Self {
        self.reverse_assertion_role_assertions = reverse_assertion_roles;
        self
    }

    // ===================================================================
    // Additional role assertions.
    // ===================================================================

    /// Port of `CIndividualProcessNode::hasAdditionalRoleAssertionsLinker`.
    pub fn has_additional_role_assertions_linker(&self) -> bool {
        self.additional_role_assertions_linker.is_some()
    }

    /// Port of `CIndividualProcessNode::clearAdditionalRoleAssertionsLinker`.
    pub fn clear_additional_role_assertions_linker(&mut self) -> &mut Self {
        self.additional_role_assertions_linker = AdditionalRoleAssertionsLinkerId::NONE;
        self
    }

    /// Port of `CIndividualProcessNode::getAdditionalRoleAssertionsLinker`.
    pub fn additional_role_assertions_linker(&self) -> AdditionalRoleAssertionsLinkerId {
        self.additional_role_assertions_linker
    }

    /// Port of `CIndividualProcessNode::setAdditionalRoleAssertionsLinker`.
    pub fn set_additional_role_assertions_linker(
        &mut self,
        reverse_role_assertions_linker: AdditionalRoleAssertionsLinkerId,
    ) -> &mut Self {
        self.additional_role_assertions_linker = reverse_role_assertions_linker;
        self
    }

    /// Port of `CIndividualProcessNode::addAdditionalRoleAssertionsLinker`.
    pub fn add_additional_role_assertions_linker(
        &mut self,
        reverse_role_assertions_linker: AdditionalRoleAssertionsLinkerId,
        process_context: &mut ProcessContext,
    ) -> &mut Self {
        // mAdditionalRoleAssertionsLinker = reverseRoleAssertionsLinker->append(mAdditionalRoleAssertionsLinker);
        if reverse_role_assertions_linker.is_some() {
            process_context
                .additional_role_assertion_linker_mut(reverse_role_assertions_linker)
                .set_next(self.additional_role_assertions_linker);
        }
        self.additional_role_assertions_linker = reverse_role_assertions_linker;
        self
    }

    // ===================================================================
    // Additional data assertions.
    // ===================================================================

    /// Port of `CIndividualProcessNode::hasAdditionalDataAssertionsLinker`.
    pub fn has_additional_data_assertions_linker(&self) -> bool {
        self.additional_data_assertions_linker.is_some()
    }

    /// Port of `CIndividualProcessNode::clearAdditionalDataAssertionsLinker`.
    pub fn clear_additional_data_assertions_linker(&mut self) -> &mut Self {
        self.additional_data_assertions_linker = AdditionalDataAssertionsLinkerId::NONE;
        self
    }

    /// Port of `CIndividualProcessNode::getAdditionalDataAssertionsLinker`.
    pub fn additional_data_assertions_linker(&self) -> AdditionalDataAssertionsLinkerId {
        self.additional_data_assertions_linker
    }

    /// Port of `CIndividualProcessNode::setAdditionalDataAssertionsLinker`.
    pub fn set_additional_data_assertions_linker(
        &mut self,
        add_data_assertions_linker: AdditionalDataAssertionsLinkerId,
    ) -> &mut Self {
        self.additional_data_assertions_linker = add_data_assertions_linker;
        self
    }

    /// Port of `CIndividualProcessNode::addAdditionalDataAssertionsLinker`.
    pub fn add_additional_data_assertions_linker(
        &mut self,
        add_data_assertions_linker: AdditionalDataAssertionsLinkerId,
        process_context: &mut ProcessContext,
    ) -> &mut Self {
        // mAdditionalDataAssertionsLinker = addDataAssertionsLinker->append(mAdditionalDataAssertionsLinker);
        if add_data_assertions_linker.is_some() {
            process_context
                .additional_data_assertion_linker_mut(add_data_assertions_linker)
                .set_next(self.additional_data_assertions_linker);
        }
        self.additional_data_assertions_linker = add_data_assertions_linker;
        self
    }

    /// Port of `CIndividualProcessNode::getLastProcessedAdditionalDataAssertionLinker`.
    pub fn last_processed_additional_data_assertion_linker(
        &self,
    ) -> AdditionalDataAssertionsLinkerId {
        self.last_processed_additional_data_assertions_linker
    }

    /// Port of `CIndividualProcessNode::setLastProcessedAdditionalDataAssertionLinker`.
    pub fn set_last_processed_additional_data_assertion_linker(
        &mut self,
        data_literal_linker: AdditionalDataAssertionsLinkerId,
    ) -> &mut Self {
        self.last_processed_additional_data_assertions_linker = data_literal_linker;
        self
    }

    // ===================================================================
    // Assertion-initialisation bool flags.
    // ===================================================================

    /// Port of `CIndividualProcessNode::hasBaseConceptsInitialized`.
    pub fn has_base_concepts_initialized(&self) -> bool {
        self.base_concepts_initialized
    }

    /// Port of `CIndividualProcessNode::setBaseConceptsInitialized`.
    pub fn set_base_concepts_initialized(&mut self, initialized: bool) -> &mut Self {
        self.base_concepts_initialized = initialized;
        self
    }

    /// Port of `CIndividualProcessNode::hasUniversallyConnectionIndividualInitialized`.
    pub fn has_universally_connection_individual_initialized(&self) -> bool {
        self.universally_connection_individual_initialized
    }

    /// Port of `CIndividualProcessNode::setUniversallyConnectionIndividualInitialized`.
    pub fn set_universally_connection_individual_initialized(
        &mut self,
        initialized: bool,
    ) -> &mut Self {
        self.universally_connection_individual_initialized = initialized;
        self
    }

    /// Port of `CIndividualProcessNode::hasRoleAssertionsInitialized`.
    pub fn has_role_assertions_initialized(&self) -> bool {
        self.role_assertions_initialized
    }

    /// Port of `CIndividualProcessNode::setRoleAssertionsInitialized`.
    pub fn set_role_assertions_initialized(&mut self, initialized: bool) -> &mut Self {
        self.role_assertions_initialized = initialized;
        self
    }

    /// Port of `CIndividualProcessNode::hasReverseRoleAssertionsInitialized`.
    pub fn has_reverse_role_assertions_initialized(&self) -> bool {
        self.reverse_role_assertions_initialized
    }

    /// Port of `CIndividualProcessNode::setReverseRoleAssertionsInitialized`.
    pub fn set_reverse_role_assertions_initialized(&mut self, initialized: bool) -> &mut Self {
        self.reverse_role_assertions_initialized = initialized;
        self
    }

    /// Port of `CIndividualProcessNode::hasNominalIndividualTriplesAssertions`.
    pub fn has_nominal_individual_triples_assertions(&self) -> bool {
        self.nominal_indi_triples_assertions
    }

    /// Port of `CIndividualProcessNode::setNominalIndividualTriplesAssertions`.
    pub fn set_nominal_individual_triples_assertions(
        &mut self,
        has_nominal_assertions: bool,
    ) -> &mut Self {
        self.nominal_indi_triples_assertions = has_nominal_assertions;
        self
    }

    /// Port of `CIndividualProcessNode::areNominalIndividualTriplesAssertionsLoaded`.
    pub fn are_nominal_individual_triples_assertions_loaded(&self) -> bool {
        self.loaded_nominal_indi_triples_assertions
    }

    /// Port of `CIndividualProcessNode::setNominalIndividualTriplesAssertionsLoaded`.
    pub fn set_nominal_individual_triples_assertions_loaded(&mut self, loaded: bool) -> &mut Self {
        self.loaded_nominal_indi_triples_assertions = loaded;
        self
    }

    /// Port of `CIndividualProcessNode::isNominalIndividualRepresentativeBackendDataLoaded`.
    pub fn is_nominal_individual_representative_backend_data_loaded(&self) -> bool {
        self.loaded_nominal_indi_representative_backend_data
    }

    /// Port of `CIndividualProcessNode::setNominalIndividualRepresentativeBackendDataLoaded`.
    pub fn set_nominal_individual_representative_backend_data_loaded(
        &mut self,
        loaded: bool,
    ) -> &mut Self {
        self.loaded_nominal_indi_representative_backend_data = loaded;
        self
    }

    // ===================================================================
    // Identity scalars (`.cpp` 816–836).
    // SKIPPED — `getIndividualNodeID`/`setIndividualNodeID`/`getIndividualType`/
    // `setIndividualType` are already inherent methods on `node.rs`; see the
    // module-level doc note (incl. the `set_individual_node_id` merge-guard
    // deviation flagged for later reconciliation).
    // ===================================================================
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::konclude_ht::process::stubs::{
        AdditionalProcessDataAssertionsLinker, AdditionalProcessRoleAssertionsLinker,
        ProcessAssertedDataLiteralLinker, ProcessContextId,
    };
    use crate::konclude_ht::process::TrackPointId;

    #[test]
    fn process_assertion_linker_asserted_data_literal_prepends_and_preserves_payload() {
        let mut ctx = ProcessContext::new();
        let mut node = IndividualProcessNode::new(ProcessContextId::NONE);
        let dep = TrackPointId::new(9);

        let mut first = ProcessAssertedDataLiteralLinker::new();
        first.init_process_data_literal_linker(11, dep);
        let first_id = ctx.alloc_process_asserted_data_literal_linker(first);
        let mut second = ProcessAssertedDataLiteralLinker::new();
        second.init_process_data_literal_linker(12, TrackPointId::new(10));
        let second_id = ctx.alloc_process_asserted_data_literal_linker(second);

        node.add_asserted_data_literal_linker(first_id, &mut ctx)
            .add_asserted_data_literal_linker(second_id, &mut ctx);

        assert_eq!(node.asserted_data_literal_linker(), second_id);
        assert_eq!(
            ctx.process_asserted_data_literal_linker(second_id).next(),
            first_id
        );
        assert_eq!(
            ctx.process_asserted_data_literal_linker(first_id).next(),
            ProcessAssertedDataLiteralLinkerId::NONE
        );
        assert_eq!(
            ctx.process_asserted_data_literal_linker(first_id)
                .data_literal(),
            11
        );
        assert_eq!(
            ctx.process_asserted_data_literal_linker(first_id)
                .dependency_track_point(),
            dep
        );
    }

    #[test]
    fn process_assertion_linker_additional_role_prepends_and_preserves_payload() {
        let mut ctx = ProcessContext::new();
        let mut node = IndividualProcessNode::new(ProcessContextId::NONE);
        let dep = TrackPointId::new(13);
        let role_head = RoleAssertionLinkerId::new(21);
        let reverse_head = ReverseRoleAssertionLinkerId::new(22);

        let mut first = AdditionalProcessRoleAssertionsLinker::new();
        first.init_additional_process_role_assertions_linker(31, role_head, reverse_head, dep);
        let first_id = ctx.alloc_additional_role_assertion_linker(first);
        let second_id = ctx
            .alloc_additional_role_assertion_linker(AdditionalProcessRoleAssertionsLinker::new());

        node.add_additional_role_assertions_linker(first_id, &mut ctx)
            .add_additional_role_assertions_linker(second_id, &mut ctx);

        assert_eq!(node.additional_role_assertions_linker(), second_id);
        assert_eq!(
            ctx.additional_role_assertion_linker(second_id).next(),
            first_id
        );
        assert_eq!(
            ctx.additional_role_assertion_linker(first_id).next(),
            AdditionalRoleAssertionsLinkerId::NONE
        );
        assert_eq!(
            ctx.additional_role_assertion_linker(first_id).individual(),
            31
        );
        assert_eq!(
            ctx.additional_role_assertion_linker(first_id)
                .role_assertion_linker(),
            role_head
        );
        assert_eq!(
            ctx.additional_role_assertion_linker(first_id)
                .reverse_role_assertion_linker(),
            reverse_head
        );
        assert_eq!(
            ctx.additional_role_assertion_linker(first_id)
                .dependency_track_point(),
            dep
        );
    }

    #[test]
    fn process_assertion_linker_additional_data_prepends_and_preserves_payload() {
        let mut ctx = ProcessContext::new();
        let mut node = IndividualProcessNode::new(ProcessContextId::NONE);
        let dep = TrackPointId::new(17);
        let data_head = DataAssertionLinkerId::new(41);

        let mut first = AdditionalProcessDataAssertionsLinker::new();
        first.init_additional_process_data_assertions_linker(51, data_head, dep);
        let first_id = ctx.alloc_additional_data_assertion_linker(first);
        let second_id = ctx
            .alloc_additional_data_assertion_linker(AdditionalProcessDataAssertionsLinker::new());

        node.add_additional_data_assertions_linker(first_id, &mut ctx)
            .add_additional_data_assertions_linker(second_id, &mut ctx);

        assert_eq!(node.additional_data_assertions_linker(), second_id);
        assert_eq!(
            ctx.additional_data_assertion_linker(second_id).next(),
            first_id
        );
        assert_eq!(
            ctx.additional_data_assertion_linker(first_id).next(),
            AdditionalDataAssertionsLinkerId::NONE
        );
        assert_eq!(
            ctx.additional_data_assertion_linker(first_id).individual(),
            51
        );
        assert_eq!(
            ctx.additional_data_assertion_linker(first_id)
                .data_assertion_linker(),
            data_head
        );
        assert_eq!(
            ctx.additional_data_assertion_linker(first_id)
                .dependency_track_point(),
            dep
        );
    }
}
