//! `process::backend_control` — backend-neighbour expansion controlling data.
//!
//! Port of
//! `Source/Reasoner/Kernel/Process/CBackendNeighbourExpansionControllingData.{h,cpp}`.

#![allow(dead_code)]

use super::super::model::substrate::Cint64;
use super::{DependencyId, NodeId, TrackPointId};

/// `CBackendNeighbourExpansionControllingData*` →
/// `BackendNeighbourExpansionControllingDataId`.
pub type BackendNeighbourExpansionControllingDataId =
    super::super::model::substrate::Id<BackendNeighbourExpansionControllingData>;

/// Port of `CBackendNeighbourExpansionControllingData`.
#[derive(Clone, Debug)]
pub struct BackendNeighbourExpansionControllingData {
    pub expanded_neighbour_link_count: Cint64,
    pub reuse_modes_dep_node: DependencyId,
    pub fixed_reuse_expansion_mode: bool,
    pub prioritized_reuse_expansion_mode: bool,
    pub reuse_continuing_dependency_track_point: TrackPointId,
    pub last_backend_expanded_ensuring_existing_individual_links_linker: Vec<NodeId>,
    pub cut_backend_neighbour_expansion_individual_linker: Vec<NodeId>,
    pub last_cut_backend_neighbour_expansion_ensuring_existing_individual_links_linker: Vec<NodeId>,
}

impl Default for BackendNeighbourExpansionControllingData {
    fn default() -> Self {
        Self {
            expanded_neighbour_link_count: 0,
            reuse_modes_dep_node: DependencyId::NONE,
            fixed_reuse_expansion_mode: false,
            prioritized_reuse_expansion_mode: false,
            reuse_continuing_dependency_track_point: TrackPointId::NONE,
            last_backend_expanded_ensuring_existing_individual_links_linker: Vec::new(),
            cut_backend_neighbour_expansion_individual_linker: Vec::new(),
            last_cut_backend_neighbour_expansion_ensuring_existing_individual_links_linker:
                Vec::new(),
        }
    }
}

impl BackendNeighbourExpansionControllingData {
    /// Port of `CBackendNeighbourExpansionControllingData(CProcessContext*)`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `initExpansionControllingData`.
    pub fn init_expansion_controlling_data(
        &mut self,
        cont_data: Option<&BackendNeighbourExpansionControllingData>,
    ) -> &mut Self {
        if let Some(cont_data) = cont_data {
            self.expanded_neighbour_link_count = cont_data.expanded_neighbour_link_count;
            self.reuse_modes_dep_node = cont_data.reuse_modes_dep_node;
            self.reuse_continuing_dependency_track_point =
                cont_data.reuse_continuing_dependency_track_point;
            self.prioritized_reuse_expansion_mode = cont_data.prioritized_reuse_expansion_mode;
            self.fixed_reuse_expansion_mode = cont_data.fixed_reuse_expansion_mode;
            self.last_backend_expanded_ensuring_existing_individual_links_linker = cont_data
                .last_backend_expanded_ensuring_existing_individual_links_linker
                .clone();
            self.cut_backend_neighbour_expansion_individual_linker = cont_data
                .cut_backend_neighbour_expansion_individual_linker
                .clone();
            self.last_cut_backend_neighbour_expansion_ensuring_existing_individual_links_linker =
                cont_data
                    .last_cut_backend_neighbour_expansion_ensuring_existing_individual_links_linker
                    .clone();
        } else {
            *self = Self::default();
        }
        self
    }

    /// Port of `getExpandedNeighbourLinkCount`.
    pub fn get_expanded_neighbour_link_count(&self) -> Cint64 {
        self.expanded_neighbour_link_count
    }

    /// Port of `incExpandedNeighbourLinkCount`.
    pub fn inc_expanded_neighbour_link_count(&mut self, count: Cint64) -> &mut Self {
        self.expanded_neighbour_link_count += count;
        self
    }

    /// Port of `getReuseModesDependencyNode`.
    pub fn get_reuse_modes_dependency_node(&self) -> DependencyId {
        self.reuse_modes_dep_node
    }

    /// Port of `setReuseModesDependencyNode`.
    pub fn set_reuse_modes_dependency_node(&mut self, dep_node: DependencyId) -> &mut Self {
        self.reuse_modes_dep_node = dep_node;
        self
    }

    /// Port of `hasExpansionReusingMode`.
    pub fn has_expansion_reusing_mode(&self) -> bool {
        self.is_fixed_reuse_expansion_mode() || self.is_prioritized_reuse_expansion_mode()
    }

    /// Port of `isFixedReuseExpansionMode`.
    pub fn is_fixed_reuse_expansion_mode(&self) -> bool {
        self.fixed_reuse_expansion_mode
    }

    /// Port of `setFixedReuseExpansionMode`.
    pub fn set_fixed_reuse_expansion_mode(&mut self, active: bool) -> &mut Self {
        self.fixed_reuse_expansion_mode = active;
        self
    }

    /// Port of `isPrioritizedReuseExpansionMode`.
    pub fn is_prioritized_reuse_expansion_mode(&self) -> bool {
        self.prioritized_reuse_expansion_mode
    }

    /// Port of `setPrioritizedReuseExpansionMode`.
    pub fn set_prioritized_reuse_expansion_mode(&mut self, active: bool) -> &mut Self {
        self.prioritized_reuse_expansion_mode = active;
        self
    }

    /// Port of `getReuseContinuingDependencyTrackPoint`.
    pub fn get_reuse_continuing_dependency_track_point(&self) -> TrackPointId {
        self.reuse_continuing_dependency_track_point
    }

    /// Port of `setReuseContinuingDependencyTrackPoint`.
    pub fn set_reuse_continuing_dependency_track_point(
        &mut self,
        dep_track_point: TrackPointId,
    ) -> &mut Self {
        self.reuse_continuing_dependency_track_point = dep_track_point;
        self
    }

    /// Port of `getLastBackendExpandedEnsuringExistingIndividualLinksLinker`.
    pub fn get_last_backend_expanded_ensuring_existing_individual_links_linker(&self) -> &[NodeId] {
        &self.last_backend_expanded_ensuring_existing_individual_links_linker
    }

    /// Port of `setLastBackendExpandedEnsuringExistingIndividualLinksLinker`.
    pub fn set_last_backend_expanded_ensuring_existing_individual_links_linker(
        &mut self,
        indi_linker: Vec<NodeId>,
    ) -> &mut Self {
        self.last_backend_expanded_ensuring_existing_individual_links_linker = indi_linker;
        self
    }

    /// Port of `getCutBackendNeighbourExpansionIndividualLinker`.
    pub fn get_cut_backend_neighbour_expansion_individual_linker(&self) -> &[NodeId] {
        &self.cut_backend_neighbour_expansion_individual_linker
    }

    /// Port of `addCutBackendNeighbourExpansionIndividualLinker`.
    pub fn add_cut_backend_neighbour_expansion_individual_linker(
        &mut self,
        mut indi_linker: Vec<NodeId>,
    ) -> &mut Self {
        if !indi_linker.is_empty() {
            indi_linker.append(&mut self.cut_backend_neighbour_expansion_individual_linker);
            self.cut_backend_neighbour_expansion_individual_linker = indi_linker;
        }
        self
    }

    /// Port of `getLastCutBackendNeighbourExpansionEnsuringExistingIndividualLinksLinker`.
    pub fn get_last_cut_backend_neighbour_expansion_ensuring_existing_individual_links_linker(
        &self,
    ) -> &[NodeId] {
        &self.last_cut_backend_neighbour_expansion_ensuring_existing_individual_links_linker
    }

    /// Port of `setLastCutBackendNeighbourExpansionEnsuringExistingIndividualLinksLinker`.
    pub fn set_last_cut_backend_neighbour_expansion_ensuring_existing_individual_links_linker(
        &mut self,
        indi_linker: Vec<NodeId>,
    ) -> &mut Self {
        self.last_cut_backend_neighbour_expansion_ensuring_existing_individual_links_linker =
            indi_linker;
        self
    }
}
