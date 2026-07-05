//! `process::concept_process_linker` — `CConceptProcessLinker`.
//!
//! Konclude implements this as `CLinkerBase<CConceptDescriptor*, Self>` plus
//! one `CProcessingRestrictionSpecification*` payload.

#![allow(dead_code)]

use super::super::model::substrate::Id;
use super::{ConDescId, RestrictionSpecId};

/// `CConceptProcessLinker*`.
pub type ConceptProcessLinkerId = Id<ConceptProcessLinker>;

/// Port of `CConceptProcessLinker`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConceptProcessLinker {
    /// `CLinkerBase` data (`getData()`).
    concept_descriptor: ConDescId,
    /// `mProcRest`.
    processing_restriction: RestrictionSpecId,
    /// Intrusive next pointer from `CLinkerBase`.
    next: ConceptProcessLinkerId,
}

impl Default for ConceptProcessLinker {
    fn default() -> Self {
        Self {
            concept_descriptor: ConDescId::NONE,
            processing_restriction: RestrictionSpecId::NONE,
            next: ConceptProcessLinkerId::NONE,
        }
    }
}

impl ConceptProcessLinker {
    /// Port of `CConceptProcessLinker::CConceptProcessLinker`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `CConceptProcessLinker::initConceptProcessLinker`.
    pub fn init_concept_process_linker(
        &mut self,
        concept_descriptor: ConDescId,
        processing_restriction: RestrictionSpecId,
    ) -> &mut Self {
        self.concept_descriptor = concept_descriptor;
        self.processing_restriction = processing_restriction;
        self.next = ConceptProcessLinkerId::NONE;
        self
    }

    /// Port of `CConceptProcessLinker::getConceptDescriptor`.
    pub fn get_concept_descriptor(&self) -> ConDescId {
        self.concept_descriptor
    }

    /// Port of `CConceptProcessLinker::getProcessingRestriction`.
    pub fn get_processing_restriction(&self) -> RestrictionSpecId {
        self.processing_restriction
    }

    /// `CLinkerBase::getNext`.
    pub fn get_next(&self) -> ConceptProcessLinkerId {
        self.next
    }

    /// `CLinkerBase::clearNext`.
    pub fn clear_next(&mut self) -> &mut Self {
        self.next = ConceptProcessLinkerId::NONE;
        self
    }

    /// `CLinkerBase::setNext`.
    pub fn set_next(&mut self, next: ConceptProcessLinkerId) -> &mut Self {
        self.next = next;
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn concept_process_linker_init_sets_descriptor_restriction_and_clears_next() {
        let mut linker = ConceptProcessLinker::new();
        linker
            .set_next(ConceptProcessLinkerId::new(9))
            .init_concept_process_linker(ConDescId::new(3), RestrictionSpecId::new(4));

        assert_eq!(linker.get_concept_descriptor(), ConDescId::new(3));
        assert_eq!(
            linker.get_processing_restriction(),
            RestrictionSpecId::new(4)
        );
        assert_eq!(linker.get_next(), ConceptProcessLinkerId::NONE);
    }
}
