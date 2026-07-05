//! `process::backend_sync` — per-node backend-cache synchronisation data.
//!
//! Port of Konclude
//! `CIndividualNodeRepresentativeMemoryBackendCacheSynchronisationData`.

#![allow(dead_code)]

use std::collections::HashMap;

use super::super::cache::backend_data::IndividualAssociationDataId;
use super::super::model::substrate::{Cint64, Id, INVALID};
use super::{ConDescId, EdgeId, NodeId, TrackPointId};

/// `CIndividualNodeRepresentativeMemoryBackendCacheSynchronisationData*`.
pub type BackendSyncDataId = Id<IndividualNodeBackendCacheSynchronisationData>;

#[derive(Clone, Debug)]
pub struct IndividualNodeBackendCacheSynchronisationData {
    pub association_data: IndividualAssociationDataId,
    pub backend_cache_synchron: bool,
    pub backend_concept_set_initialized: bool,
    pub backend_concept_set_initialization_required: bool,
    pub backend_concept_set_initialization_queued: bool,
    pub backend_concept_set_initialization_delaying_registered: bool,
    pub non_concept_set_backend_label_related_processing: bool,
    pub non_concept_set_backend_neighbour_label_related_processing: bool,
    pub critical_cardinality_expansion_blocking: bool,
    pub critical_cardinality_initially_checked: bool,
    pub critical_neighbour_expansion_blocking: bool,
    pub critical_indirect_connection_individual_expansion_blocking: bool,
    pub all_neighbour_expansion: bool,
    pub all_neighbour_expansion_scheduled: bool,
    pub all_neighbour_forced_expansion: bool,
    pub all_neighbour_forced_expansion_scheduled: bool,
    pub neighbour_label_representative_expansion: bool,
    pub nominal_indirect_connection_individual_expanded: bool,
    pub merged_indirectly_connected_nominal_individuals: bool,
    pub reuse_non_deterministic_same_individual_merged: bool,
    pub reuse_non_deterministic_concepts_added: bool,
    pub reuse_non_deterministic_different_individual_stated: bool,
    pub non_deterministically_merged_individuals: bool,
    pub scheduled_individual: NodeId,
    pub backend_expansion_reuse_dependency_track_point: TrackPointId,
    pub merged_individual_node_linker: Vec<NodeId>,
    pub last_synchronized_concepts_tested_merged_node_linker: Vec<NodeId>,
    pub last_critical_neighbours_tested_merged_node_linker: Vec<NodeId>,
    pub last_direct_expansion_handled_merged_node_linker: Vec<NodeId>,
    pub last_inferring_expansion_handled_merged_node_linker: Vec<NodeId>,
    pub last_indirectly_connected_nominal_individuals_tested_merged_node_linker: Vec<NodeId>,
    pub last_indirectly_connected_nominal_individuals_handled_merged_node_linker: Vec<NodeId>,
    pub last_synched_concept_descriptor: ConDescId,
    pub last_synchronization_tested_concept_descriptor: ConDescId,
    pub last_critical_neighbour_expansion_tested_concept_descriptor: ConDescId,
    pub last_indirect_connected_individual_expansion_tested_concept_descriptor: ConDescId,
    pub last_critical_cardinality_link_edge: EdgeId,
    pub last_indirect_connected_individual_expansion_tested_link_edge: EdgeId,
    pub concept_set_label_processed_node_linker: Vec<NodeId>,
    pub neighbour_label_representative_expansion_linker: Vec<Cint64>,
    pub backend_neighbour_expansion_queue: Cint64,
    pub neighbour_expansion_data_hash: HashMap<Cint64, Cint64>,
    pub neighbour_label_expansion_data_hash: HashMap<Cint64, HashMap<Cint64, Cint64>>,
    pub role_neighbour_expansion_data_hash: HashMap<Cint64, Cint64>,
    pub role_representative_neighbour_count_hash: HashMap<Cint64, Cint64>,
}

impl Default for IndividualNodeBackendCacheSynchronisationData {
    fn default() -> Self {
        Self {
            association_data: Id::NONE,
            backend_cache_synchron: false,
            backend_concept_set_initialized: false,
            backend_concept_set_initialization_required: false,
            backend_concept_set_initialization_queued: false,
            backend_concept_set_initialization_delaying_registered: false,
            non_concept_set_backend_label_related_processing: false,
            non_concept_set_backend_neighbour_label_related_processing: false,
            critical_cardinality_expansion_blocking: false,
            critical_cardinality_initially_checked: false,
            critical_neighbour_expansion_blocking: false,
            critical_indirect_connection_individual_expansion_blocking: false,
            all_neighbour_expansion: false,
            all_neighbour_expansion_scheduled: false,
            all_neighbour_forced_expansion: false,
            all_neighbour_forced_expansion_scheduled: false,
            neighbour_label_representative_expansion: false,
            nominal_indirect_connection_individual_expanded: false,
            merged_indirectly_connected_nominal_individuals: false,
            reuse_non_deterministic_same_individual_merged: false,
            reuse_non_deterministic_concepts_added: false,
            reuse_non_deterministic_different_individual_stated: false,
            non_deterministically_merged_individuals: false,
            scheduled_individual: Id::NONE,
            backend_expansion_reuse_dependency_track_point: Id::NONE,
            merged_individual_node_linker: Vec::new(),
            last_synchronized_concepts_tested_merged_node_linker: Vec::new(),
            last_critical_neighbours_tested_merged_node_linker: Vec::new(),
            last_direct_expansion_handled_merged_node_linker: Vec::new(),
            last_inferring_expansion_handled_merged_node_linker: Vec::new(),
            last_indirectly_connected_nominal_individuals_tested_merged_node_linker: Vec::new(),
            last_indirectly_connected_nominal_individuals_handled_merged_node_linker: Vec::new(),
            last_synched_concept_descriptor: Id::NONE,
            last_synchronization_tested_concept_descriptor: Id::NONE,
            last_critical_neighbour_expansion_tested_concept_descriptor: Id::NONE,
            last_indirect_connected_individual_expansion_tested_concept_descriptor: Id::NONE,
            last_critical_cardinality_link_edge: Id::NONE,
            last_indirect_connected_individual_expansion_tested_link_edge: Id::NONE,
            concept_set_label_processed_node_linker: Vec::new(),
            neighbour_label_representative_expansion_linker: Vec::new(),
            backend_neighbour_expansion_queue: INVALID,
            neighbour_expansion_data_hash: HashMap::new(),
            neighbour_label_expansion_data_hash: HashMap::new(),
            role_neighbour_expansion_data_hash: HashMap::new(),
            role_representative_neighbour_count_hash: HashMap::new(),
        }
    }
}

impl IndividualNodeBackendCacheSynchronisationData {
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `initSynchronisationData`.
    pub fn init_synchronisation_data(
        &mut self,
        prev: Option<&IndividualNodeBackendCacheSynchronisationData>,
    ) -> &mut Self {
        if let Some(prev) = prev {
            *self = prev.clone();
        } else {
            *self = Self::default();
        }
        self
    }

    pub fn get_associtaion_data(&self) -> IndividualAssociationDataId {
        self.association_data
    }

    pub fn set_associtaion_data(
        &mut self,
        association_data: IndividualAssociationDataId,
    ) -> &mut Self {
        self.association_data = association_data;
        self
    }

    pub fn is_backend_cache_synchron(&self) -> bool {
        self.backend_cache_synchron
    }

    pub fn set_backend_cache_synchron(&mut self, active: bool) -> &mut Self {
        self.backend_cache_synchron = active;
        self
    }

    pub fn set_backend_concept_set_initialized(&mut self, active: bool) -> &mut Self {
        self.backend_concept_set_initialized = active;
        self
    }

    pub fn set_backend_concept_set_initialization_required(&mut self, active: bool) -> &mut Self {
        self.backend_concept_set_initialization_required = active;
        self
    }

    pub fn is_backend_concept_set_initialization_queued(&self) -> bool {
        self.backend_concept_set_initialization_queued
    }

    pub fn set_backend_concept_set_initialization_queued(&mut self, active: bool) -> &mut Self {
        self.backend_concept_set_initialization_queued = active;
        self
    }

    pub fn is_backend_concept_set_initialization_delaying_registered(&self) -> bool {
        self.backend_concept_set_initialization_delaying_registered
    }

    pub fn set_backend_concept_set_initialization_delaying_registered(
        &mut self,
        active: bool,
    ) -> &mut Self {
        self.backend_concept_set_initialization_delaying_registered = active;
        self
    }

    pub fn has_non_concept_set_backend_label_related_processing(&self) -> bool {
        self.non_concept_set_backend_label_related_processing
    }

    pub fn set_non_concept_set_backend_label_related_processing(
        &mut self,
        active: bool,
    ) -> &mut Self {
        self.non_concept_set_backend_label_related_processing = active;
        self
    }

    pub fn has_non_concept_set_backend_neighbour_label_related_processing(&self) -> bool {
        self.non_concept_set_backend_neighbour_label_related_processing
    }

    pub fn set_non_concept_set_backend_neighbour_label_related_processing(
        &mut self,
        active: bool,
    ) -> &mut Self {
        self.non_concept_set_backend_neighbour_label_related_processing = active;
        self
    }

    pub fn is_critical_cardinality_expansion_blocking(&self) -> bool {
        self.critical_cardinality_expansion_blocking
    }

    pub fn set_critical_cardinality_expansion_blocking(&mut self, active: bool) -> &mut Self {
        self.critical_cardinality_expansion_blocking = active;
        self
    }

    pub fn has_critical_cardinality_initially_checked(&self) -> bool {
        self.critical_cardinality_initially_checked
    }

    pub fn set_critical_cardinality_initially_checked(&mut self, active: bool) -> &mut Self {
        self.critical_cardinality_initially_checked = active;
        self
    }

    pub fn is_critical_neighbour_expansion_blocking(&self) -> bool {
        self.critical_neighbour_expansion_blocking
    }

    pub fn set_critical_neighbour_expansion_blocking(&mut self, active: bool) -> &mut Self {
        self.critical_neighbour_expansion_blocking = active;
        self
    }

    pub fn is_critical_indirect_connection_individual_expansion_blocking(&self) -> bool {
        self.critical_indirect_connection_individual_expansion_blocking
    }

    pub fn set_critical_indirect_connection_individual_expansion_blocking(
        &mut self,
        active: bool,
    ) -> &mut Self {
        self.critical_indirect_connection_individual_expansion_blocking = active;
        self
    }

    pub fn has_all_neighbour_expansion_scheduled(&self) -> bool {
        self.all_neighbour_expansion_scheduled
    }

    pub fn set_all_neighbour_expansion_scheduled(&mut self, active: bool) -> &mut Self {
        self.all_neighbour_expansion_scheduled = active;
        self
    }

    pub fn set_all_neighbour_expansion(&mut self, active: bool) -> &mut Self {
        self.all_neighbour_expansion = active;
        self
    }

    pub fn has_all_neighbour_forced_expansion_scheduled(&self) -> bool {
        self.all_neighbour_forced_expansion_scheduled
    }

    pub fn set_all_neighbour_forced_expansion_scheduled(&mut self, active: bool) -> &mut Self {
        self.all_neighbour_forced_expansion_scheduled = active;
        self
    }

    pub fn has_all_neighbour_forced_expansion(&self) -> bool {
        self.all_neighbour_forced_expansion
    }

    pub fn set_all_neighbour_forced_expansion(&mut self, active: bool) -> &mut Self {
        self.all_neighbour_forced_expansion = active;
        self
    }

    pub fn has_neighbour_label_representative_expansion(&self) -> bool {
        self.neighbour_label_representative_expansion
    }

    pub fn set_neighbour_label_representative_expansion(&mut self, active: bool) -> &mut Self {
        self.neighbour_label_representative_expansion = active;
        self
    }

    pub fn has_neighbour_label_representative_expansion_installed(&self) -> bool {
        !self
            .neighbour_label_representative_expansion_linker
            .is_empty()
    }

    pub fn install_neighbour_label_representative_expansion(
        &mut self,
        linker: Cint64,
    ) -> &mut Self {
        self.neighbour_label_representative_expansion_linker
            .push(linker);
        self
    }

    pub fn get_neighbour_label_representative_expansion_linker(&self) -> &[Cint64] {
        &self.neighbour_label_representative_expansion_linker
    }

    pub fn clear_neighbour_label_representative_expansion_linker(&mut self) -> &mut Self {
        self.neighbour_label_representative_expansion_linker.clear();
        self
    }

    pub fn set_nominal_indirect_connection_individual_expanded(
        &mut self,
        active: bool,
    ) -> &mut Self {
        self.nominal_indirect_connection_individual_expanded = active;
        self
    }

    pub fn has_merged_indirectly_connected_nominal_individuals(&self) -> bool {
        self.merged_indirectly_connected_nominal_individuals
    }

    pub fn set_merged_indirectly_connected_nominal_individuals(
        &mut self,
        active: bool,
    ) -> &mut Self {
        self.merged_indirectly_connected_nominal_individuals = active;
        self
    }

    pub fn has_reuse_non_deterministic_same_individual_merged(&self) -> bool {
        self.reuse_non_deterministic_same_individual_merged
    }

    pub fn set_reuse_non_deterministic_same_individual_merged(
        &mut self,
        active: bool,
    ) -> &mut Self {
        self.reuse_non_deterministic_same_individual_merged = active;
        self
    }

    pub fn has_reuse_non_deterministic_concepts_added(&self) -> bool {
        self.reuse_non_deterministic_concepts_added
    }

    pub fn set_reuse_non_deterministic_concepts_added(&mut self, active: bool) -> &mut Self {
        self.reuse_non_deterministic_concepts_added = active;
        self
    }

    pub fn has_reuse_non_deterministic_different_individual_stated(&self) -> bool {
        self.reuse_non_deterministic_different_individual_stated
    }

    pub fn set_reuse_non_deterministic_different_individual_stated(
        &mut self,
        active: bool,
    ) -> &mut Self {
        self.reuse_non_deterministic_different_individual_stated = active;
        self
    }

    pub fn has_non_deterministically_merged_individuals(&self) -> bool {
        self.non_deterministically_merged_individuals
    }

    pub fn set_scheduled_individual(&mut self, individual: NodeId) -> &mut Self {
        self.scheduled_individual = individual;
        self
    }

    pub fn get_backend_expansion_reuse_dependency_track_point(&self) -> TrackPointId {
        self.backend_expansion_reuse_dependency_track_point
    }

    pub fn set_backend_expansion_reuse_dependency_track_point(
        &mut self,
        dep_track_point: TrackPointId,
    ) -> &mut Self {
        self.backend_expansion_reuse_dependency_track_point = dep_track_point;
        self
    }

    pub fn get_merged_individual_node_linker(&self) -> &[NodeId] {
        &self.merged_individual_node_linker
    }

    pub fn get_last_synchronized_concepts_tested_merged_node_linker(&self) -> &[NodeId] {
        &self.last_synchronized_concepts_tested_merged_node_linker
    }

    pub fn set_last_synchronized_concepts_tested_merged_node_linker(
        &mut self,
        linker: Vec<NodeId>,
    ) -> &mut Self {
        self.last_synchronized_concepts_tested_merged_node_linker = linker;
        self
    }

    pub fn get_last_critical_neighbours_tested_merged_node_linker(&self) -> &[NodeId] {
        &self.last_critical_neighbours_tested_merged_node_linker
    }

    pub fn set_last_critical_neighbours_tested_merged_node_linker(
        &mut self,
        linker: Vec<NodeId>,
    ) -> &mut Self {
        self.last_critical_neighbours_tested_merged_node_linker = linker;
        self
    }

    pub fn get_last_direct_expansion_handled_merged_node_linker(&self) -> &[NodeId] {
        &self.last_direct_expansion_handled_merged_node_linker
    }

    pub fn set_last_direct_expansion_handled_merged_node_linker(
        &mut self,
        linker: Vec<NodeId>,
    ) -> &mut Self {
        self.last_direct_expansion_handled_merged_node_linker = linker;
        self
    }

    pub fn get_last_inferring_expansion_handled_merged_node_linker(&self) -> &[NodeId] {
        &self.last_inferring_expansion_handled_merged_node_linker
    }

    pub fn set_last_inferring_expansion_handled_merged_node_linker(
        &mut self,
        linker: Vec<NodeId>,
    ) -> &mut Self {
        self.last_inferring_expansion_handled_merged_node_linker = linker;
        self
    }

    pub fn get_last_indirectly_connected_nominal_individuals_tested_merged_node_linker(
        &self,
    ) -> &[NodeId] {
        &self.last_indirectly_connected_nominal_individuals_tested_merged_node_linker
    }

    pub fn set_last_indirectly_connected_nominal_individuals_tested_merged_node_linker(
        &mut self,
        linker: Vec<NodeId>,
    ) -> &mut Self {
        self.last_indirectly_connected_nominal_individuals_tested_merged_node_linker = linker;
        self
    }

    pub fn set_last_indirectly_connected_nominal_individuals_handled_merged_node_linker(
        &mut self,
        linker: Vec<NodeId>,
    ) -> &mut Self {
        self.last_indirectly_connected_nominal_individuals_handled_merged_node_linker = linker;
        self
    }

    pub fn get_last_synched_concept_descriptor(&self) -> ConDescId {
        self.last_synched_concept_descriptor
    }

    pub fn set_last_synched_concept_descriptor(&mut self, con_des: ConDescId) -> &mut Self {
        self.last_synched_concept_descriptor = con_des;
        self
    }

    pub fn get_last_synchronization_tested_concept_descriptor(&self) -> ConDescId {
        self.last_synchronization_tested_concept_descriptor
    }

    pub fn set_last_synchronization_tested_concept_descriptor(
        &mut self,
        con_des: ConDescId,
    ) -> &mut Self {
        self.last_synchronization_tested_concept_descriptor = con_des;
        self
    }

    pub fn get_last_critical_neighbour_expansion_tested_concept_descriptor(&self) -> ConDescId {
        self.last_critical_neighbour_expansion_tested_concept_descriptor
    }

    pub fn set_last_critical_neighbour_expansion_tested_concept_descriptor(
        &mut self,
        con_des: ConDescId,
    ) -> &mut Self {
        self.last_critical_neighbour_expansion_tested_concept_descriptor = con_des;
        self
    }

    pub fn get_last_indirect_connected_individual_expansion_tested_concept_descriptor(
        &self,
    ) -> ConDescId {
        self.last_indirect_connected_individual_expansion_tested_concept_descriptor
    }

    pub fn set_last_indirect_connected_individual_expansion_tested_concept_descriptor(
        &mut self,
        con_des: ConDescId,
    ) -> &mut Self {
        self.last_indirect_connected_individual_expansion_tested_concept_descriptor = con_des;
        self
    }

    pub fn get_last_critical_cardinality_link_edge(&self) -> EdgeId {
        self.last_critical_cardinality_link_edge
    }

    pub fn set_last_critical_cardinality_link_edge(&mut self, edge: EdgeId) -> &mut Self {
        self.last_critical_cardinality_link_edge = edge;
        self
    }

    pub fn get_last_indirect_connected_individual_expansion_tested_link_edge(&self) -> EdgeId {
        self.last_indirect_connected_individual_expansion_tested_link_edge
    }

    pub fn set_last_indirect_connected_individual_expansion_tested_link_edge(
        &mut self,
        edge: EdgeId,
    ) -> &mut Self {
        self.last_indirect_connected_individual_expansion_tested_link_edge = edge;
        self
    }

    pub fn set_concept_set_label_processed_node_linker(
        &mut self,
        linker: Vec<NodeId>,
    ) -> &mut Self {
        self.concept_set_label_processed_node_linker = linker;
        self
    }

    pub fn get_backend_neighbour_expansion_queue(&self, _create: bool) -> Cint64 {
        self.backend_neighbour_expansion_queue
    }

    pub fn get_neighbour_expansion_data_hash(
        &mut self,
        _create: bool,
    ) -> &mut HashMap<Cint64, Cint64> {
        &mut self.neighbour_expansion_data_hash
    }

    pub fn get_neighbour_label_expansion_data_hash(
        &mut self,
        array_id: Cint64,
        _create: bool,
    ) -> &mut HashMap<Cint64, Cint64> {
        self.neighbour_label_expansion_data_hash
            .entry(array_id)
            .or_default()
    }

    pub fn get_role_neighbour_expansion_data_hash(
        &mut self,
        _create: bool,
    ) -> &mut HashMap<Cint64, Cint64> {
        &mut self.role_neighbour_expansion_data_hash
    }

    pub fn get_role_representative_neighbour_count_hash(
        &mut self,
        _create: bool,
    ) -> &mut HashMap<Cint64, Cint64> {
        &mut self.role_representative_neighbour_count_hash
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::konclude_ht::process::context::ProcessContext;
    use crate::konclude_ht::process::node::IndividualProcessNode;

    #[test]
    fn backend_sync_data_init_copies_konclude_state_fields() {
        let mut ctx = ProcessContext::new();
        let node = ctx.alloc_node(IndividualProcessNode::new(Id::NONE));
        let con_des = ctx.alloc_con_desc(Default::default());
        let edge = ctx.alloc_edge(Default::default());
        let mut data = IndividualNodeBackendCacheSynchronisationData::new();
        data.set_backend_cache_synchron(true)
            .set_critical_cardinality_expansion_blocking(true)
            .set_critical_cardinality_initially_checked(true)
            .set_last_critical_neighbour_expansion_tested_concept_descriptor(con_des)
            .set_last_critical_cardinality_link_edge(edge)
            .set_last_critical_neighbours_tested_merged_node_linker(vec![node]);

        let mut copied = IndividualNodeBackendCacheSynchronisationData::new();
        copied.init_synchronisation_data(Some(&data));

        assert!(copied.is_backend_cache_synchron());
        assert!(copied.is_critical_cardinality_expansion_blocking());
        assert!(copied.has_critical_cardinality_initially_checked());
        assert_eq!(
            copied.get_last_critical_neighbour_expansion_tested_concept_descriptor(),
            con_des
        );
        assert_eq!(copied.get_last_critical_cardinality_link_edge(), edge);
        assert_eq!(
            copied.get_last_critical_neighbours_tested_merged_node_linker(),
            &[node]
        );
    }

    #[test]
    fn backend_sync_context_alloc_from_prev_preserves_previous_snapshot() {
        let mut ctx = ProcessContext::new();
        let mut data = IndividualNodeBackendCacheSynchronisationData::new();
        data.set_all_neighbour_forced_expansion(true)
            .set_reuse_non_deterministic_concepts_added(true);
        let prev = ctx.alloc_backend_sync_data(data);

        let localized = ctx.alloc_backend_sync_data_from_prev(prev);

        assert!(ctx
            .backend_sync_data(localized)
            .has_all_neighbour_forced_expansion());
        assert!(ctx
            .backend_sync_data(localized)
            .has_reuse_non_deterministic_concepts_added());
        assert_ne!(prev, localized);
    }
}
