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
use super::{ClashDescId, ConDescId, ConProcDescId, RestrictionSpecId, TrackPointId};

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

/// Port of `CClashedDependencyDescriptor` (base `CLinkerBase`).
///
/// The base record of the clash-descriptor family (unsat detection): just a
/// dependency track point plus the intrusive next-descriptor link.
///
/// KONCLUDE-PORT-NOTE[unclear]: `CClashedDependencyDescriptor` has a `virtual`
/// destructor and is subclassed by the concrete clash kinds
/// (`CClashedConceptDescriptor`, `CClashedIndividualLinkDescriptor`,
/// `CClashedIndividualDistinctDescriptor`, `CClashedNegationDisjointLinkDescriptor`,
/// `CClashedDatatypeValueSpaceExclusionDescriptor`). The polymorphic family is
/// to be folded into a tagged enum in a later SD unit
/// (`manifest/05` §1 names it `ClashedDescriptor`); this struct ports only the
/// shared base for now.
pub struct ClashDescriptor {
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

    // W2 method-batch: `initClashedDependencyDescriptor` + the per-subclass clash
    // payloads (concept / link / distinct / negation-disjoint / datatype),
    // deferred to the clash tagged-enum unit.
}
