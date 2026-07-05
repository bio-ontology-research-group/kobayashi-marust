//! `process::edge` — port of Konclude's completion-graph edge records
//! (`Reasoner/Kernel/Process/`): the role link edge plus the two extra binary
//! edge kinds (differentFrom / negated-disjoint). SD-1 struct unit per
//! `manifest/05-process-units.md`.
//!
//! Konclude's edge classes form a small inheritance chain that Rust cannot
//! express with implementation inheritance, so the base fields are inlined and
//! tagged. The chain is:
//!
//! ```text
//! CProcessTag        { mProcessTag }
//!   └ CLocalizationTag { mRelocalized }      (CProcessTag base)
//!       └ CNodeEdge      { mSourceIndividual, mDestinationIndividual }
//!                          (+ CDependencyTracker { mDependencyTrackPoint })
//!           └ CLinkEdge    { mRole }
//!               └ CNegationDisjointEdge        -> DisjointEdge
//!           └ CDistinctEdge                    -> DistinctEdge
//!       CIndividualLinkEdge { mCreatorIndividual }  (CLinkEdge + CLinkerBase self-chain)
//!                                              -> IndividualLinkEdge
//! ```
//!
//! KONCLUDE-PORT-NOTE[ownership]: every raw `CIndividualProcessNode*` /
//! `CRole*` / `CDependencyTrackPoint*` field becomes a typed arena id
//! (`NodeId` / `RoleId` / `TrackPointId`); `Id::NONE` == `nullptr`. The
//! `CLinkerBase<CIndividualLinkEdge*>` intrusive self-chain becomes a `next:
//! EdgeId` field (the faithful representation of the singly-linked edge list a
//! node keeps; a flat arena-order `Vec` is the behaviour-neutral faster
//! alternative). See `substrate.rs` for the global `[ownership]` rationale.

#![allow(dead_code)]

use super::super::model::substrate::Cint64;
use super::super::model::RoleId;
use super::{EdgeId, NodeId, TrackPointId};

/// Port of `CIndividualLinkEdge` (folding bases `CNodeEdge`, `CLinkEdge`).
///
/// A directed role edge `source --role--> destination` recorded during
/// completion, tagging the creator node and the dependency track point that
/// justifies it.
pub struct IndividualLinkEdge {
    // --- inherited from CProcessTag ---
    /// `CProcessTag::mProcessTag` (relocalization / localization tag).
    pub process_tag: Cint64,
    // --- inherited from CLocalizationTag ---
    /// `CLocalizationTag::mRelocalized`.
    pub relocalized: bool,
    // --- inherited from CDependencyTracker ---
    // KONCLUDE-PORT-NOTE[ownership]: `CDependencyTrackPoint* mDependencyTrackPoint` -> `TrackPointId`.
    /// `CDependencyTracker::mDependencyTrackPoint`.
    pub dep_track_point: TrackPointId,
    // --- inherited from CNodeEdge ---
    // KONCLUDE-PORT-NOTE[ownership]: `CIndividualProcessNode* mSourceIndividual` -> `NodeId`.
    /// `CNodeEdge::mSourceIndividual`.
    pub source: NodeId,
    // KONCLUDE-PORT-NOTE[ownership]: `CIndividualProcessNode* mDestinationIndividual` -> `NodeId`.
    /// `CNodeEdge::mDestinationIndividual`.
    pub destination: NodeId,
    // --- inherited from CLinkEdge ---
    // KONCLUDE-PORT-NOTE[ownership]: `CRole* mRole` -> `RoleId`.
    /// `CLinkEdge::mRole`.
    pub role: RoleId,
    // --- CIndividualLinkEdge own ---
    // KONCLUDE-PORT-NOTE[ownership]: `CIndividualProcessNode* mCreatorIndividual` -> `NodeId`.
    /// `CIndividualLinkEdge::mCreatorIndividual`.
    pub creator: NodeId,
    // KONCLUDE-PORT-NOTE[ownership]: `CLinkerBase<CIndividualLinkEdge*>` intrusive
    // self-chain -> `next: EdgeId`. `Id::NONE` == end of list.
    /// `CLinkerBase` next link.
    pub next: EdgeId,
}

impl Default for IndividualLinkEdge {
    fn default() -> Self {
        IndividualLinkEdge {
            process_tag: 0,
            relocalized: false,
            dep_track_point: TrackPointId::NONE,
            source: NodeId::NONE,
            destination: NodeId::NONE,
            role: RoleId::NONE,
            creator: NodeId::NONE,
            next: EdgeId::NONE,
        }
    }
}

impl IndividualLinkEdge {
    /// Port of `CIndividualLinkEdge::CIndividualLinkEdge` (default ctor).
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `CIndividualLinkEdge::initIndividualLinkEdge(CIndividualProcessNode*, ...)`.
    pub fn init_individual_link_edge(
        &mut self,
        creator: NodeId,
        source: NodeId,
        destination: NodeId,
        role: RoleId,
        dep_track_point: TrackPointId,
    ) -> &mut Self {
        self.creator = creator;
        self.source = source;
        self.destination = destination;
        self.role = role;
        self.dep_track_point = dep_track_point;
        self.next = EdgeId::NONE;
        self
    }

    /// Port of `CIndividualLinkEdge::initIndividualLinkEdge(CIndividualLinkEdge*)`.
    pub fn init_individual_link_edge_from(&mut self, link: &IndividualLinkEdge) -> &mut Self {
        self.process_tag = link.process_tag;
        self.relocalized = link.relocalized;
        self.dep_track_point = link.dep_track_point;
        self.source = link.source;
        self.destination = link.destination;
        self.role = link.role;
        self.creator = link.creator;
        self.next = EdgeId::NONE;
        self
    }

    // --- simple field accessors ---
    /// Port of `CNodeEdge::getSourceIndividual`.
    pub fn get_source_individual(&self) -> NodeId {
        self.source
    }
    /// Port of `CNodeEdge::setSourceIndividual`.
    pub fn set_source_individual(&mut self, indi: NodeId) -> &mut Self {
        self.source = indi;
        self
    }
    /// Port of `CNodeEdge::getDestinationIndividual`.
    pub fn get_destination_individual(&self) -> NodeId {
        self.destination
    }
    /// Port of `CNodeEdge::setDestinationIndividual`.
    pub fn set_destination_individual(&mut self, indi: NodeId) -> &mut Self {
        self.destination = indi;
        self
    }
    /// Port of `CLinkEdge::getLinkRole`.
    pub fn get_link_role(&self) -> RoleId {
        self.role
    }
    /// Port of `CLinkEdge::setLinkRole`.
    pub fn set_link_role(&mut self, role: RoleId) -> &mut Self {
        self.role = role;
        self
    }
    /// Port of `CIndividualLinkEdge::getCreatorIndividual`.
    pub fn get_creator_individual(&self) -> NodeId {
        self.creator
    }
    /// Port of `CDependencyTracker::getDependencyTrackPoint`.
    pub fn get_dependency_track_point(&self) -> TrackPointId {
        self.dep_track_point
    }
    /// Port of `CDependencyTracker::setDependencyTrackPoint`.
    pub fn set_dependency_track_point(&mut self, tp: TrackPointId) -> &mut Self {
        self.dep_track_point = tp;
        self
    }
    /// Port of `CLocalizationTag::isRelocalized`.
    pub fn is_relocalized(&self) -> bool {
        self.relocalized
    }
    /// Port of `CLocalizationTag::setRelocalized`.
    pub fn set_relocalized(&mut self, relocalized: bool) -> &mut Self {
        self.relocalized = relocalized;
        self
    }
    /// Port of `CLocalizationTag::isLocalizationTagUpToDate(cint64)`
    /// (→ `CProcessTag::isProcessTagUpToDate`: `mProcessTag >= processTag`). The edge
    /// localization tag is the inherited `CProcessTag::mProcessTag` (`process_tag`).
    /// `getSuccessorIndividual` reads this against the current localization tag.
    pub fn is_localization_tag_up_to_date(&self, localization_tag: Cint64) -> bool {
        self.process_tag >= localization_tag
    }
    /// `CLinkerBase::getNext` (next edge in the intrusive chain).
    pub fn get_next(&self) -> EdgeId {
        self.next
    }
    /// `CLinkerBase::setNext`.
    pub fn set_next(&mut self, next: EdgeId) -> &mut Self {
        self.next = next;
        self
    }

    // W2 method-batch (edge derived): `getCreatorIndividualID`,
    // `isCreatorIndividual`, `isCreatorIndividualID` (both overloads), and the inherited
    // `CNodeEdge::getSourceIndividualID`/`getDestinationIndividualID`/
    // `getOppositeIndividual(ID)`/`isSourceIndividualID`/`isDestinationIndividualID`/
    // `getCoupledIndividualID` (these dereference the node ids and need the
    // node arena, deferred).
}

/// Port of `CDistinctEdge` (base `CNodeEdge`).
///
/// An `owl:differentFrom` edge between two nodes; carries no role and no
/// creator (it extends only `CNodeEdge`).
pub struct DistinctEdge {
    /// `CProcessTag::mProcessTag`.
    pub process_tag: Cint64,
    /// `CLocalizationTag::mRelocalized`.
    pub relocalized: bool,
    // KONCLUDE-PORT-NOTE[ownership]: `CDependencyTrackPoint*` -> `TrackPointId`.
    /// `CDependencyTracker::mDependencyTrackPoint`.
    pub dep_track_point: TrackPointId,
    // KONCLUDE-PORT-NOTE[ownership]: `CIndividualProcessNode*` -> `NodeId`.
    /// `CNodeEdge::mSourceIndividual`.
    pub source: NodeId,
    // KONCLUDE-PORT-NOTE[ownership]: `CIndividualProcessNode*` -> `NodeId`.
    /// `CNodeEdge::mDestinationIndividual`.
    pub destination: NodeId,
}

impl Default for DistinctEdge {
    fn default() -> Self {
        DistinctEdge {
            process_tag: 0,
            relocalized: false,
            dep_track_point: TrackPointId::NONE,
            source: NodeId::NONE,
            destination: NodeId::NONE,
        }
    }
}

impl DistinctEdge {
    /// Port of `CDistinctEdge::CDistinctEdge` (default ctor).
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `CDistinctEdge::initDistinctEdge`.
    ///
    /// C++ assigns the inherited source/destination node pointers and dependency
    /// track point, then returns `this`.
    pub fn init_distinct_edge(
        &mut self,
        source: NodeId,
        destination: NodeId,
        dep_track_point: TrackPointId,
    ) -> &mut Self {
        self.source = source;
        self.destination = destination;
        self.dep_track_point = dep_track_point;
        self
    }

    /// Port of `CNodeEdge::getSourceIndividual`.
    pub fn get_source_individual(&self) -> NodeId {
        self.source
    }
    /// Port of `CNodeEdge::setSourceIndividual`.
    pub fn set_source_individual(&mut self, indi: NodeId) -> &mut Self {
        self.source = indi;
        self
    }
    /// Port of `CNodeEdge::getDestinationIndividual`.
    pub fn get_destination_individual(&self) -> NodeId {
        self.destination
    }
    /// Port of `CNodeEdge::setDestinationIndividual`.
    pub fn set_destination_individual(&mut self, indi: NodeId) -> &mut Self {
        self.destination = indi;
        self
    }
    /// Port of `CDependencyTracker::getDependencyTrackPoint`.
    pub fn get_dependency_track_point(&self) -> TrackPointId {
        self.dep_track_point
    }
    /// Port of `CDependencyTracker::setDependencyTrackPoint`.
    pub fn set_dependency_track_point(&mut self, tp: TrackPointId) -> &mut Self {
        self.dep_track_point = tp;
        self
    }
    /// Port of `CLocalizationTag::isRelocalized`.
    pub fn is_relocalized(&self) -> bool {
        self.relocalized
    }
    /// Port of `CLocalizationTag::setRelocalized`.
    pub fn set_relocalized(&mut self, relocalized: bool) -> &mut Self {
        self.relocalized = relocalized;
        self
    }

    // W2 method-batch (edge derived): the inherited `CNodeEdge` *ID / opposite /
    // coupled accessors (need the node arena).
}

/// Port of `CNegationDisjointEdge` (base `CLinkEdge`).
///
/// A negated disjoint-role edge `source --role--> destination`; carries a role
/// (from `CLinkEdge`) but no creator.
///
/// KONCLUDE-PORT-NOTE[api]: the canonical Rust name is `DisjointEdge`
/// (`process/mod.rs` `DisjointEdgeId = Id<edge::DisjointEdge>`); the C++ class
/// is `CNegationDisjointEdge`.
pub struct DisjointEdge {
    /// `CProcessTag::mProcessTag`.
    pub process_tag: Cint64,
    /// `CLocalizationTag::mRelocalized`.
    pub relocalized: bool,
    // KONCLUDE-PORT-NOTE[ownership]: `CDependencyTrackPoint*` -> `TrackPointId`.
    /// `CDependencyTracker::mDependencyTrackPoint`.
    pub dep_track_point: TrackPointId,
    // KONCLUDE-PORT-NOTE[ownership]: `CIndividualProcessNode*` -> `NodeId`.
    /// `CNodeEdge::mSourceIndividual`.
    pub source: NodeId,
    // KONCLUDE-PORT-NOTE[ownership]: `CIndividualProcessNode*` -> `NodeId`.
    /// `CNodeEdge::mDestinationIndividual`.
    pub destination: NodeId,
    // KONCLUDE-PORT-NOTE[ownership]: `CRole*` -> `RoleId`.
    /// `CLinkEdge::mRole`.
    pub role: RoleId,
}

impl Default for DisjointEdge {
    fn default() -> Self {
        DisjointEdge {
            process_tag: 0,
            relocalized: false,
            dep_track_point: TrackPointId::NONE,
            source: NodeId::NONE,
            destination: NodeId::NONE,
            role: RoleId::NONE,
        }
    }
}

impl DisjointEdge {
    /// Port of `CNegationDisjointEdge::CNegationDisjointEdge` (default ctor).
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `CNegationDisjointEdge::initNegationDisjointEdge`.
    pub fn init_negation_disjoint_edge(
        &mut self,
        source: NodeId,
        destination: NodeId,
        role: RoleId,
        dep_track_point: TrackPointId,
    ) -> &mut Self {
        self.source = source;
        self.destination = destination;
        self.role = role;
        self.dep_track_point = dep_track_point;
        self
    }

    /// Port of `CNodeEdge::getSourceIndividual`.
    pub fn get_source_individual(&self) -> NodeId {
        self.source
    }
    /// Port of `CNodeEdge::setSourceIndividual`.
    pub fn set_source_individual(&mut self, indi: NodeId) -> &mut Self {
        self.source = indi;
        self
    }
    /// Port of `CNodeEdge::getDestinationIndividual`.
    pub fn get_destination_individual(&self) -> NodeId {
        self.destination
    }
    /// Port of `CNodeEdge::setDestinationIndividual`.
    pub fn set_destination_individual(&mut self, indi: NodeId) -> &mut Self {
        self.destination = indi;
        self
    }
    /// Port of `CLinkEdge::getLinkRole`.
    pub fn get_link_role(&self) -> RoleId {
        self.role
    }
    /// Port of `CLinkEdge::setLinkRole`.
    pub fn set_link_role(&mut self, role: RoleId) -> &mut Self {
        self.role = role;
        self
    }
    /// Port of `CDependencyTracker::getDependencyTrackPoint`.
    pub fn get_dependency_track_point(&self) -> TrackPointId {
        self.dep_track_point
    }
    /// Port of `CDependencyTracker::setDependencyTrackPoint`.
    pub fn set_dependency_track_point(&mut self, tp: TrackPointId) -> &mut Self {
        self.dep_track_point = tp;
        self
    }
    /// Port of `CLocalizationTag::isRelocalized`.
    pub fn is_relocalized(&self) -> bool {
        self.relocalized
    }
    /// Port of `CLocalizationTag::setRelocalized`.
    pub fn set_relocalized(&mut self, relocalized: bool) -> &mut Self {
        self.relocalized = relocalized;
        self
    }

    // W2 method-batch (edge derived): the inherited `CNodeEdge` *ID / opposite /
    // coupled accessors need the node arena.
}
