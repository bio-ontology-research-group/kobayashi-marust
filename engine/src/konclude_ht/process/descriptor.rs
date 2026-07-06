//! `process::descriptor` — port of Konclude's concept-occurrence descriptors and
//! the clash-descriptor base (`Reasoner/Kernel/Process/`). SD-1 struct unit per
//! `manifest/05-process-units.md`.
//!
//! Three records:
//!   * `ConceptDescriptor` (`CConceptDescriptor`) — a (concept, polarity) pair
//!     with the dependency track point that introduced it, intrusively chained.
//!   * `ConceptProcessDescriptor` (`CConceptProcessDescriptor`) — a queued
//!     concept descriptor with its processing priority / restriction spec.
//!   * `ClashDescriptor` (`CClashedDependencyDescriptor`) — the base of the
//!     clash-record family (unsat detection).
//!
//! KONCLUDE-PORT-NOTE[ownership]: raw `CXxx*` fields become typed arena ids;
//! `Id::NONE` == `nullptr`. The `CNegLinkerBase` / `CSortedLinkerBase` /
//! `CLinkerBase` intrusive self-chains become explicit `next: …Id` fields. See
//! `substrate.rs` for the global `[ownership]` rationale.

#![allow(dead_code)]

use super::super::model::ontology::OntologyArenas;
use super::super::model::substrate::Cint64;
use super::super::model::ConceptId;
use super::varbind::VarBindingPathId;
use super::{
    ClashDescId, ConDescId, ConProcDescId, DisjointEdgeId, DistinctEdgeId, EdgeId, NodeId,
    RestrictionSpecId, TrackPointId,
};

/// Port of `CConceptProcessPriority`.
///
/// A small value object (a single `double mPriority`) embedded by value in
/// `ConceptProcessDescriptor`. Ported here rather than as its own arena id
/// because it is a value, not a pooled pointer target.
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct ConceptProcessPriority {
    /// `CConceptProcessPriority::mPriority`.
    pub priority: f64,
}

impl Default for ConceptProcessPriority {
    fn default() -> Self {
        ConceptProcessPriority { priority: 0.0 }
    }
}

impl ConceptProcessPriority {
    /// Port of `CConceptProcessPriority::CConceptProcessPriority(double)`.
    pub fn new(priority: f64) -> Self {
        ConceptProcessPriority { priority }
    }
    /// Port of `CConceptProcessPriority::getPriority`.
    pub fn get_priority(&self) -> f64 {
        self.priority
    }
    /// Port of `CConceptProcessPriority::setPriority`.
    pub fn set_priority(&mut self, priority: f64) -> &mut Self {
        self.priority = priority;
        self
    }
    /// Port of `CConceptProcessPriority::addPriorityOffset`.
    pub fn add_priority_offset(&mut self, offset: f64) -> &mut Self {
        self.priority += offset;
        self
    }
    // W2 method-batch: comparison operators `==`/`!=`/`<=`/`>=`/`<`/`>`
    // (port as `PartialOrd`/`Ord` impls over `priority`).
}

/// Port of `CConceptDescriptor` (bases `CNegLinkerBase<CConcept*>`,
/// `CDependencyTracker`).
///
/// A concept occurrence with a negation polarity, the track point that justifies
/// it, and the intrusive next-descriptor link.
#[derive(Clone)]
pub struct ConceptDescriptor {
    // --- from CNegLinkerBase<CConcept*> ---
    // KONCLUDE-PORT-NOTE[ownership]: `CConcept*` linker target -> `ConceptId`.
    /// `CNegLinkerBase` data (the described concept).
    pub concept: ConceptId,
    /// `CNegLinkerBase` negation bit.
    pub negated: bool,
    // KONCLUDE-PORT-NOTE[ownership]: `CNegLinkerBase` intrusive self-chain ->
    // `next: ConDescId`. `Id::NONE` == end of list.
    /// `CNegLinkerBase` next link (`getNextConceptDesciptor`).
    pub next: ConDescId,
    // --- from CDependencyTracker ---
    // KONCLUDE-PORT-NOTE[ownership]: `CDependencyTrackPoint*` -> `TrackPointId`.
    /// `CDependencyTracker::mDependencyTrackPoint`.
    pub dep_track_point: TrackPointId,
}

impl Default for ConceptDescriptor {
    fn default() -> Self {
        ConceptDescriptor {
            concept: ConceptId::NONE,
            negated: false,
            next: ConDescId::NONE,
            dep_track_point: TrackPointId::NONE,
        }
    }
}

impl ConceptDescriptor {
    /// Port of `CConceptDescriptor::CConceptDescriptor` (default ctor).
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `CConceptDescriptor::getConcept`.
    pub fn get_concept(&self) -> ConceptId {
        self.concept
    }
    /// `CNegLinkerBase` negation bit.
    pub fn is_negated(&self) -> bool {
        self.negated
    }
    /// Port of `CConceptDescriptor::getNextConceptDesciptor`.
    pub fn get_next_concept_descriptor(&self) -> ConDescId {
        self.next
    }
    /// `CNegLinkerBase::setNext`.
    pub fn set_next(&mut self, next: ConDescId) -> &mut Self {
        self.next = next;
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

    /// Port of `CConceptDescriptor::getConceptTag` (`return getData()->getConceptTag()`).
    ///
    /// KONCLUDE-PORT-NOTE[pointer-alias]: C++ `getData()` is the wrapped
    /// `CConcept*` (here `self.concept: ConceptId`); resolve it against the static
    /// concept terminology to read `CConcept::getConceptTag()`. This un-defers the
    /// `getConceptTag` member of the W2 method-batch that left the concept-arena
    /// deref pending; it is what `ReapplyConceptLabelSetIterator::get_data_tag`'s
    /// linker branch now calls.
    pub fn get_concept_tag(&self, onto: &OntologyArenas) -> Cint64 {
        onto.concept(self.concept).get_concept_tag()
    }

    // W2 method-batch (descriptor derived): `initConceptDescriptor`,
    // `isEqualsToBOTTOM`, `isEqualsToTOP`, `getTerminologyTag`,
    // `getTerminologyConceptTagPair`, `isClashWith` (these dereference the
    // concept arena / operator codes, deferred).
}

/// Port of `CConceptProcessDescriptor` (base `CSortedLinkerBase`).
///
/// A concept descriptor queued for processing, carrying its priority, the
/// justifying track point, an optional processing-restriction spec, and a
/// "reapplied" flag.
///
/// KONCLUDE-PORT-NOTE[ownership]: all fields are `Copy` (ids / priority / bool),
/// so the struct derives `Copy`; `CConceptProcessDescriptor::initCopy` (a
/// field-wise copy) is realised as `*dst = *src`.
#[derive(Copy, Clone)]
pub struct ConceptProcessDescriptor {
    // KONCLUDE-PORT-NOTE[ownership]: `CConceptDescriptor* conceptDes` -> `ConDescId`.
    /// `CConceptProcessDescriptor::conceptDes`.
    pub concept_des: ConDescId,
    /// `CConceptProcessDescriptor::priority`.
    pub priority: ConceptProcessPriority,
    // KONCLUDE-PORT-NOTE[ownership]: `CDependencyTrackPoint* depTrackPoint` -> `TrackPointId`.
    /// `CConceptProcessDescriptor::depTrackPoint`.
    pub dep_track_point: TrackPointId,
    // KONCLUDE-PORT-NOTE[ownership]: `CProcessingRestrictionSpecification* mProcSpec` -> `RestrictionSpecId`.
    /// `CConceptProcessDescriptor::mProcSpec`.
    pub proc_spec: RestrictionSpecId,
    /// `CConceptProcessDescriptor::mReapplied`.
    pub reapplied: bool,
    // KONCLUDE-PORT-NOTE[ownership]: `CSortedLinkerBase` intrusive self-chain ->
    // `next: ConProcDescId`. `Id::NONE` == end of list.
    /// `CSortedLinkerBase` next link.
    pub next: ConProcDescId,
}

impl Default for ConceptProcessDescriptor {
    fn default() -> Self {
        ConceptProcessDescriptor {
            concept_des: ConDescId::NONE,
            priority: ConceptProcessPriority::default(),
            dep_track_point: TrackPointId::NONE,
            proc_spec: RestrictionSpecId::NONE,
            reapplied: false,
            next: ConProcDescId::NONE,
        }
    }
}

impl ConceptProcessDescriptor {
    /// Port of `CConceptProcessDescriptor::CConceptProcessDescriptor` (default ctor).
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `CConceptProcessDescriptor::getConceptDescriptor`.
    pub fn get_concept_descriptor(&self) -> ConDescId {
        self.concept_des
    }
    /// Port of `CConceptProcessDescriptor::getProcessPriority`.
    pub fn get_process_priority(&self) -> ConceptProcessPriority {
        self.priority
    }
    /// Port of `CConceptProcessDescriptor::getDependencyTrackPoint`.
    pub fn get_dependency_track_point(&self) -> TrackPointId {
        self.dep_track_point
    }
    /// Port of `CConceptProcessDescriptor::isConceptReapplied`.
    pub fn is_concept_reapplied(&self) -> bool {
        self.reapplied
    }
    /// Port of `CConceptProcessDescriptor::getProcessingRestrictionSpecification`.
    pub fn get_processing_restriction_specification(&self) -> RestrictionSpecId {
        self.proc_spec
    }
    /// `CSortedLinkerBase::getNext`.
    pub fn get_next(&self) -> ConProcDescId {
        self.next
    }
    /// `CSortedLinkerBase::setNext`.
    pub fn set_next(&mut self, next: ConProcDescId) -> &mut Self {
        self.next = next;
        self
    }

    // W2 method-batch: `init` (full ctor), `initCopy`, and `operator<=`
    // (the sorted-linker ordering, ported as `PartialOrd`).
}

/// The concrete payload folded into [`ClashDescriptor`].
///
/// KONCLUDE-PORT-NOTE[template]: Konclude represents clash descriptors with a
/// small subclass family. The port keeps the existing single arena and records
/// the runtime subtype in this enum.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ClashDescriptorKind {
    /// Base `CClashedDependencyDescriptor` only.
    Dependency,
    /// `CClashedConceptDescriptor`.
    Concept {
        /// `CClashedConceptDescriptor::mConceptDescriptor`.
        concept_descriptor: ConDescId,
        /// `CClashedConceptDescriptor::mIndividualNode`.
        individual_node: NodeId,
    },
    /// `CClashedIndividualLinkDescriptor`.
    IndividualLink {
        /// `CClashedIndividualLinkDescriptor::mLinkEdge`.
        link_edge: EdgeId,
    },
    /// `CClashedIndividualDistinctDescriptor`.
    IndividualDistinct {
        /// `CClashedIndividualDistinctDescriptor::mLinkEdge`.
        distinct_edge: DistinctEdgeId,
    },
    /// `CClashedNegationDisjointLinkDescriptor`.
    NegationDisjointLink {
        /// `CClashedNegationDisjointLinkDescriptor::mLinkEdge`.
        disjoint_edge: DisjointEdgeId,
    },
    /// `CTrackedClashedDescriptor`.
    Tracked {
        /// `CTrackedClashedDescriptor::mIndiNode`.
        individual_node: NodeId,
        /// `CTrackedClashedDescriptor::mIndiNodeID`.
        individual_node_id: Cint64,
        /// `CTrackedClashedDescriptor::mIndiNodeLevel`.
        individual_node_level: Cint64,
        /// `CTrackedClashedDescriptor::mBranchingLevelTag`.
        branching_level_tag: Cint64,
        /// `CTrackedClashedDescriptor::mProcessingTag`.
        processing_tag: Cint64,
        /// `CTrackedClashedDescriptor::mDetermisticFlag`.
        deterministic: bool,
        /// `CTrackedClashedDescriptor::mNominalIndiFlag`.
        nominal_individual: bool,
        /// `CTrackedClashedDescriptor::mErrorFlag`.
        error: bool,
        /// `CTrackedClashedDescriptor::mIndepenentFlag`.
        independent: bool,
        /// `CTrackedClashedDescriptor::mConceptDescriptor`.
        concept_descriptor: ConDescId,
        /// `CTrackedClashedDescriptor::mVarBindPath`.
        var_bind_path: VarBindingPathId,
    },
}

impl Default for ClashDescriptorKind {
    fn default() -> Self {
        ClashDescriptorKind::Dependency
    }
}

/// Port of `CClashedDependencyDescriptor` (base `CLinkerBase`).
///
/// The base record of the clash-descriptor family (unsat detection): just a
/// dependency track point plus the intrusive next-descriptor link.
///
/// KONCLUDE-PORT-NOTE[folded]: `CClashedDependencyDescriptor` has a `virtual`
/// destructor and is subclassed by the concrete clash kinds. The port folds the
/// live non-datatype clash subclasses and `CTrackedClashedDescriptor` into
/// `ClashDescriptorKind`; the datatype value-space exclusion subclass remains
/// pending on datatype clash substrate.
#[derive(Clone)]
pub struct ClashDescriptor {
    /// Folded runtime subtype payload.
    pub kind: ClashDescriptorKind,
    // KONCLUDE-PORT-NOTE[ownership]: `CDependencyTrackPoint* mDependencyTrackPoint` -> `TrackPointId`.
    /// `CClashedDependencyDescriptor::mDependencyTrackPoint`.
    pub dep_track_point: TrackPointId,
    // KONCLUDE-PORT-NOTE[ownership]: `CLinkerBase` intrusive self-chain ->
    // `next: ClashDescId`. `Id::NONE` == end of list.
    /// `CLinkerBase` next link.
    pub next: ClashDescId,
}

impl Default for ClashDescriptor {
    fn default() -> Self {
        ClashDescriptor {
            kind: ClashDescriptorKind::Dependency,
            dep_track_point: TrackPointId::NONE,
            next: ClashDescId::NONE,
        }
    }
}

impl ClashDescriptor {
    /// Port of `CClashedDependencyDescriptor::CClashedDependencyDescriptor` (default ctor).
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `CClashedDependencyDescriptor::getDependencyTrackPoint`.
    pub fn get_dependency_track_point(&self) -> TrackPointId {
        self.dep_track_point
    }
    /// `CDependencyTracker`-style setter (`initClashedDependencyDescriptor` body).
    pub fn set_dependency_track_point(&mut self, tp: TrackPointId) -> &mut Self {
        self.dep_track_point = tp;
        self
    }
    /// `CLinkerBase::getNext`.
    pub fn get_next(&self) -> ClashDescId {
        self.next
    }
    /// `CLinkerBase::setNext`.
    pub fn set_next(&mut self, next: ClashDescId) -> &mut Self {
        self.next = next;
        self
    }

    /// Port of `CClashedDependencyDescriptor::initClashedDependencyDescriptor`.
    pub fn init_clashed_dependency_descriptor(
        &mut self,
        dep_track_point: TrackPointId,
    ) -> &mut Self {
        self.dep_track_point = dep_track_point;
        self.kind = ClashDescriptorKind::Dependency;
        self
    }

    /// Port of `CClashedConceptDescriptor::initClashedConceptDescriptor`.
    pub fn init_clashed_concept_descriptor(
        &mut self,
        concept_descriptor: ConDescId,
        dep_track_point: TrackPointId,
        individual: NodeId,
    ) -> &mut Self {
        self.init_clashed_dependency_descriptor(dep_track_point);
        self.kind = ClashDescriptorKind::Concept {
            concept_descriptor,
            individual_node: individual,
        };
        self
    }

    /// Port of `CClashedConceptDescriptor::getConceptDescriptor`.
    pub fn get_concept_descriptor(&self) -> ConDescId {
        match self.kind {
            ClashDescriptorKind::Concept {
                concept_descriptor, ..
            } => concept_descriptor,
            ClashDescriptorKind::Dependency
            | ClashDescriptorKind::IndividualLink { .. }
            | ClashDescriptorKind::IndividualDistinct { .. }
            | ClashDescriptorKind::NegationDisjointLink { .. } => ConDescId::NONE,
            ClashDescriptorKind::Tracked {
                concept_descriptor, ..
            } => concept_descriptor,
        }
    }

    /// Port of `CClashedConceptDescriptor::getAppropriatedIndividual`.
    pub fn get_appropriated_individual(&self) -> NodeId {
        match self.kind {
            ClashDescriptorKind::Concept {
                individual_node, ..
            } => individual_node,
            ClashDescriptorKind::Dependency
            | ClashDescriptorKind::IndividualLink { .. }
            | ClashDescriptorKind::IndividualDistinct { .. }
            | ClashDescriptorKind::NegationDisjointLink { .. } => NodeId::NONE,
            ClashDescriptorKind::Tracked {
                individual_node, ..
            } => individual_node,
        }
    }

    /// Port of `CClashedConceptDescriptor::setAppropriatedIndividual`.
    pub fn set_appropriated_individual(&mut self, individual_node: NodeId) -> &mut Self {
        match self.kind {
            ClashDescriptorKind::Concept {
                concept_descriptor, ..
            } => {
                self.kind = ClashDescriptorKind::Concept {
                    concept_descriptor,
                    individual_node,
                };
            }
            ClashDescriptorKind::Tracked {
                individual_node_id,
                individual_node_level,
                branching_level_tag,
                processing_tag,
                deterministic,
                nominal_individual,
                error,
                independent,
                concept_descriptor,
                var_bind_path,
                ..
            } => {
                self.kind = ClashDescriptorKind::Tracked {
                    individual_node,
                    individual_node_id,
                    individual_node_level,
                    branching_level_tag,
                    processing_tag,
                    deterministic,
                    nominal_individual,
                    error,
                    independent,
                    concept_descriptor,
                    var_bind_path,
                };
            }
            ClashDescriptorKind::Dependency
            | ClashDescriptorKind::IndividualLink { .. }
            | ClashDescriptorKind::IndividualDistinct { .. }
            | ClashDescriptorKind::NegationDisjointLink { .. } => {}
        }
        self
    }

    /// Port of `CClashedConceptDescriptor::getAppropriatedIndividualID`.
    pub fn get_appropriated_individual_id(&self) -> Cint64 {
        match self.kind {
            ClashDescriptorKind::Concept {
                individual_node, ..
            } => individual_node.raw,
            ClashDescriptorKind::Dependency
            | ClashDescriptorKind::IndividualLink { .. }
            | ClashDescriptorKind::IndividualDistinct { .. }
            | ClashDescriptorKind::NegationDisjointLink { .. } => 0,
            ClashDescriptorKind::Tracked {
                individual_node_id, ..
            } => individual_node_id,
        }
    }

    /// Port of `CClashedIndividualLinkDescriptor::initClashedLinkDescriptor`.
    pub fn init_clashed_link_descriptor(
        &mut self,
        link_edge: EdgeId,
        dep_track_point: TrackPointId,
    ) -> &mut Self {
        self.init_clashed_dependency_descriptor(dep_track_point);
        self.kind = ClashDescriptorKind::IndividualLink { link_edge };
        self
    }

    /// Port of `CClashedIndividualLinkDescriptor::getIndividualLinkEdge`.
    pub fn get_individual_link_edge(&self) -> EdgeId {
        match self.kind {
            ClashDescriptorKind::IndividualLink { link_edge } => link_edge,
            ClashDescriptorKind::Dependency
            | ClashDescriptorKind::Concept { .. }
            | ClashDescriptorKind::IndividualDistinct { .. }
            | ClashDescriptorKind::NegationDisjointLink { .. }
            | ClashDescriptorKind::Tracked { .. } => EdgeId::NONE,
        }
    }

    /// Port of `CClashedIndividualDistinctDescriptor::initClashedDistinctDescriptor`.
    pub fn init_clashed_distinct_descriptor(
        &mut self,
        distinct_edge: DistinctEdgeId,
        dep_track_point: TrackPointId,
    ) -> &mut Self {
        self.init_clashed_dependency_descriptor(dep_track_point);
        self.kind = ClashDescriptorKind::IndividualDistinct { distinct_edge };
        self
    }

    /// Port of `CClashedIndividualDistinctDescriptor::getDistinctEdge`.
    pub fn get_distinct_edge(&self) -> DistinctEdgeId {
        match self.kind {
            ClashDescriptorKind::IndividualDistinct { distinct_edge } => distinct_edge,
            ClashDescriptorKind::Dependency
            | ClashDescriptorKind::Concept { .. }
            | ClashDescriptorKind::IndividualLink { .. }
            | ClashDescriptorKind::NegationDisjointLink { .. }
            | ClashDescriptorKind::Tracked { .. } => DistinctEdgeId::NONE,
        }
    }

    /// Port of `CClashedNegationDisjointLinkDescriptor::initClashedLinkDescriptor`.
    pub fn init_clashed_negation_disjoint_link_descriptor(
        &mut self,
        disjoint_edge: DisjointEdgeId,
        dep_track_point: TrackPointId,
    ) -> &mut Self {
        self.init_clashed_dependency_descriptor(dep_track_point);
        self.kind = ClashDescriptorKind::NegationDisjointLink { disjoint_edge };
        self
    }

    /// Port of `CClashedNegationDisjointLinkDescriptor::getNegationDisjointLinkEdge`.
    pub fn get_negation_disjoint_link_edge(&self) -> DisjointEdgeId {
        match self.kind {
            ClashDescriptorKind::NegationDisjointLink { disjoint_edge } => disjoint_edge,
            ClashDescriptorKind::Dependency
            | ClashDescriptorKind::Concept { .. }
            | ClashDescriptorKind::IndividualLink { .. }
            | ClashDescriptorKind::IndividualDistinct { .. }
            | ClashDescriptorKind::Tracked { .. } => DisjointEdgeId::NONE,
        }
    }

    /// Port of `CTrackedClashedDescriptor::initTrackedClashedDescriptor`.
    pub fn init_tracked_clashed_descriptor(
        &mut self,
        individual_node: NodeId,
        individual_node_id: Cint64,
        individual_node_level: Cint64,
        nominal_individual: bool,
        concept_descriptor: ConDescId,
        var_bind_path: VarBindingPathId,
        dep_track_point: TrackPointId,
        deterministic: bool,
        independent: bool,
        processing_tag: Cint64,
        branching_level_tag: Cint64,
        error: bool,
    ) -> &mut Self {
        self.init_clashed_dependency_descriptor(dep_track_point);
        self.kind = ClashDescriptorKind::Tracked {
            individual_node,
            individual_node_id,
            individual_node_level,
            branching_level_tag,
            processing_tag,
            deterministic,
            nominal_individual,
            error,
            independent,
            concept_descriptor,
            var_bind_path,
        };
        self
    }

    /// Port of `CTrackedClashedDescriptor::initTrackedClashedDescriptor(CTrackedClashedDescriptor*)`.
    pub fn init_tracked_clashed_descriptor_copy(&mut self, tracked_clash_des: &Self) -> &mut Self {
        self.dep_track_point = tracked_clash_des.dep_track_point;
        self.kind = tracked_clash_des.kind;
        self.next = ClashDescId::NONE;
        self
    }

    /// Port of `CTrackedClashedDescriptor::getNextDescriptor`.
    pub fn get_next_descriptor(&self) -> ClashDescId {
        self.get_next()
    }

    /// Port of `CTrackedClashedDescriptor::setConceptDescriptor`.
    pub fn set_concept_descriptor(&mut self, con_des: ConDescId) -> &mut Self {
        if let ClashDescriptorKind::Tracked {
            individual_node,
            individual_node_id,
            individual_node_level,
            branching_level_tag,
            processing_tag,
            deterministic,
            nominal_individual,
            error,
            independent,
            var_bind_path,
            ..
        } = self.kind
        {
            self.kind = ClashDescriptorKind::Tracked {
                individual_node,
                individual_node_id,
                individual_node_level,
                branching_level_tag,
                processing_tag,
                deterministic,
                nominal_individual,
                error,
                independent,
                concept_descriptor: con_des,
                var_bind_path,
            };
        }
        self
    }

    /// Port of `CTrackedClashedDescriptor::getVariableBindingPath`.
    pub fn get_variable_binding_path(&self) -> VarBindingPathId {
        match self.kind {
            ClashDescriptorKind::Tracked { var_bind_path, .. } => var_bind_path,
            ClashDescriptorKind::Dependency
            | ClashDescriptorKind::Concept { .. }
            | ClashDescriptorKind::IndividualLink { .. }
            | ClashDescriptorKind::IndividualDistinct { .. }
            | ClashDescriptorKind::NegationDisjointLink { .. } => VarBindingPathId::NONE,
        }
    }

    /// Port of `CTrackedClashedDescriptor::getAppropriatedIndividualLevel`.
    pub fn get_appropriated_individual_level(&self) -> Cint64 {
        match self.kind {
            ClashDescriptorKind::Tracked {
                individual_node_level,
                ..
            } => individual_node_level,
            ClashDescriptorKind::Dependency
            | ClashDescriptorKind::Concept { .. }
            | ClashDescriptorKind::IndividualLink { .. }
            | ClashDescriptorKind::IndividualDistinct { .. }
            | ClashDescriptorKind::NegationDisjointLink { .. } => -1,
        }
    }

    /// Port of `CTrackedClashedDescriptor::getBranchingLevelTag`.
    pub fn get_branching_level_tag(&self) -> Cint64 {
        match self.kind {
            ClashDescriptorKind::Tracked {
                branching_level_tag,
                ..
            } => branching_level_tag,
            ClashDescriptorKind::Dependency
            | ClashDescriptorKind::Concept { .. }
            | ClashDescriptorKind::IndividualLink { .. }
            | ClashDescriptorKind::IndividualDistinct { .. }
            | ClashDescriptorKind::NegationDisjointLink { .. } => -1,
        }
    }

    /// Port of `CTrackedClashedDescriptor::getProcessingTag`.
    pub fn get_processing_tag(&self) -> Cint64 {
        match self.kind {
            ClashDescriptorKind::Tracked { processing_tag, .. } => processing_tag,
            ClashDescriptorKind::Dependency
            | ClashDescriptorKind::Concept { .. }
            | ClashDescriptorKind::IndividualLink { .. }
            | ClashDescriptorKind::IndividualDistinct { .. }
            | ClashDescriptorKind::NegationDisjointLink { .. } => -1,
        }
    }

    /// Port of `CTrackedClashedDescriptor::isAppropriatedIndividualNominal`.
    pub fn is_appropriated_individual_nominal(&self) -> bool {
        match self.kind {
            ClashDescriptorKind::Tracked {
                nominal_individual, ..
            } => nominal_individual,
            ClashDescriptorKind::Dependency
            | ClashDescriptorKind::Concept { .. }
            | ClashDescriptorKind::IndividualLink { .. }
            | ClashDescriptorKind::IndividualDistinct { .. }
            | ClashDescriptorKind::NegationDisjointLink { .. } => false,
        }
    }

    /// Port of `CTrackedClashedDescriptor::isPointingToDeterministicDependencyNode`.
    pub fn is_pointing_to_deterministic_dependency_node(&self) -> bool {
        match self.kind {
            ClashDescriptorKind::Tracked { deterministic, .. } => deterministic,
            ClashDescriptorKind::Dependency
            | ClashDescriptorKind::Concept { .. }
            | ClashDescriptorKind::IndividualLink { .. }
            | ClashDescriptorKind::IndividualDistinct { .. }
            | ClashDescriptorKind::NegationDisjointLink { .. } => false,
        }
    }

    /// Port of `CTrackedClashedDescriptor::isPointingToNonDeterministicDependencyNode`.
    pub fn is_pointing_to_non_deterministic_dependency_node(&self) -> bool {
        !self.is_pointing_to_deterministic_dependency_node()
    }

    /// Port of `CTrackedClashedDescriptor::isPointingToIndependentDependencyNode`.
    pub fn is_pointing_to_independent_dependency_node(&self) -> bool {
        match self.kind {
            ClashDescriptorKind::Tracked { independent, .. } => independent,
            ClashDescriptorKind::Dependency
            | ClashDescriptorKind::Concept { .. }
            | ClashDescriptorKind::IndividualLink { .. }
            | ClashDescriptorKind::IndividualDistinct { .. }
            | ClashDescriptorKind::NegationDisjointLink { .. } => false,
        }
    }

    /// Port of `CTrackedClashedDescriptor::isTrackingError`.
    pub fn is_tracking_error(&self) -> bool {
        match self.kind {
            ClashDescriptorKind::Tracked { error, .. } => error,
            ClashDescriptorKind::Dependency
            | ClashDescriptorKind::Concept { .. }
            | ClashDescriptorKind::IndividualLink { .. }
            | ClashDescriptorKind::IndividualDistinct { .. }
            | ClashDescriptorKind::NegationDisjointLink { .. } => false,
        }
    }

    // W2 method-batch: the remaining per-subclass clash payload (datatype) is
    // still deferred.
}
