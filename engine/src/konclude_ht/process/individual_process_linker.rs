//! `process::individual_process_linker` — port of `CIndividualProcessNodeLinker`.
//!
//! Konclude implements this as
//! `CNegLinkerBase<CIndividualProcessNode*, CIndividualProcessNodeLinker>`: the
//! data pointer is the process node, and the negation bit stores whether the
//! node is already queued for processing.

#![allow(dead_code)]

use super::super::model::substrate::Id;
use super::NodeId;

/// `CIndividualProcessNodeLinker*`.
pub type IndividualProcessNodeLinkerId = Id<IndividualProcessNodeLinker>;

/// Port of `CIndividualProcessNodeLinker`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IndividualProcessNodeLinker {
    /// `CNegLinkerBase` data (`getData()`).
    pub processing_individual: NodeId,
    /// `CNegLinkerBase` negation bit (`isNegated()`).
    pub processing_queued: bool,
    /// Intrusive next pointer from the linker base.
    pub next: IndividualProcessNodeLinkerId,
}

impl Default for IndividualProcessNodeLinker {
    fn default() -> Self {
        Self {
            processing_individual: NodeId::NONE,
            processing_queued: false,
            next: IndividualProcessNodeLinkerId::NONE,
        }
    }
}

impl IndividualProcessNodeLinker {
    /// Port of `CIndividualProcessNodeLinker::CIndividualProcessNodeLinker`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `CIndividualProcessNodeLinker::initProcessNodeLinker`.
    pub fn init_process_node_linker(
        &mut self,
        individual: NodeId,
        processing_queued: bool,
    ) -> &mut Self {
        self.processing_individual = individual;
        self.processing_queued = processing_queued;
        self.next = IndividualProcessNodeLinkerId::NONE;
        self
    }

    /// Port of `CIndividualProcessNodeLinker::getProcessingIndividual`.
    pub fn get_processing_individual(&self) -> NodeId {
        self.processing_individual
    }

    /// Port of `CIndividualProcessNodeLinker::isProcessingQueued`.
    pub fn is_processing_queued(&self) -> bool {
        self.processing_queued
    }

    /// Port of `CIndividualProcessNodeLinker::clearProcessingQueued`.
    pub fn clear_processing_queued(&mut self) -> &mut Self {
        self.processing_queued = false;
        self
    }

    /// Port of `CIndividualProcessNodeLinker::setProcessingQueued`.
    ///
    /// The C++ implementation ignores its argument and always calls
    /// `setNegation(true)`. This port preserves that behaviour exactly.
    pub fn set_processing_queued(&mut self, _processing_queued: bool) -> &mut Self {
        self.processing_queued = true;
        self
    }

    /// Port of `CLinkerBase::getNext`.
    pub fn get_next(&self) -> IndividualProcessNodeLinkerId {
        self.next
    }

    /// Port of `CLinkerBase::setNext`.
    pub fn set_next(&mut self, next: IndividualProcessNodeLinkerId) -> &mut Self {
        self.next = next;
        self
    }

    /// Port of `CLinkerBase::clearNext`.
    pub fn clear_next(&mut self) -> &mut Self {
        self.next = IndividualProcessNodeLinkerId::NONE;
        self
    }
}
