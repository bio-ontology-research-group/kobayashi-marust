//! `process::sat_linker` — port of `CIndividualSaturationProcessNodeLinker`.
//!
//! Konclude implements this as `CNegLinkerBase<CIndividualSaturationProcessNode*, Self>`:
//! the data pointer is the saturation node, and the negation bit stores whether
//! the node is currently queued for processing.

#![allow(dead_code)]

use super::super::model::substrate::Id;
use super::SatNodeId;

/// `CIndividualSaturationProcessNodeLinker*`.
pub type IndividualSaturationProcessNodeLinkerId = Id<IndividualSaturationProcessNodeLinker>;

/// Port of `CIndividualSaturationProcessNodeLinker`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IndividualSaturationProcessNodeLinker {
    /// `CNegLinkerBase` data (`getData()`).
    pub processing_individual: SatNodeId,
    /// `CNegLinkerBase` negation bit (`isNegated()`).
    pub processing_queued: bool,
    /// Intrusive next pointer from the linker base.
    pub next: IndividualSaturationProcessNodeLinkerId,
}

impl Default for IndividualSaturationProcessNodeLinker {
    fn default() -> Self {
        Self {
            processing_individual: SatNodeId::NONE,
            processing_queued: false,
            next: IndividualSaturationProcessNodeLinkerId::NONE,
        }
    }
}

impl IndividualSaturationProcessNodeLinker {
    /// Port of `CIndividualSaturationProcessNodeLinker::CIndividualSaturationProcessNodeLinker`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `initProcessNodeLinker`.
    pub fn init_process_node_linker(
        &mut self,
        individual: SatNodeId,
        processing_queued: bool,
    ) -> &mut Self {
        self.processing_individual = individual;
        self.processing_queued = processing_queued;
        self.next = IndividualSaturationProcessNodeLinkerId::NONE;
        self
    }

    /// Port of `getProcessingIndividual`.
    pub fn get_processing_individual(&self) -> SatNodeId {
        self.processing_individual
    }

    /// Port of `isProcessingQueued`.
    pub fn is_processing_queued(&self) -> bool {
        self.processing_queued
    }

    /// Port of `clearProcessingQueued`.
    pub fn clear_processing_queued(&mut self) -> &mut Self {
        self.processing_queued = false;
        self
    }

    /// Port of `setProcessingQueued`.
    pub fn set_processing_queued(&mut self, processing_queued: bool) -> &mut Self {
        self.processing_queued = processing_queued;
        self
    }

    /// `CLinkerBase::getNext`.
    pub fn get_next(&self) -> IndividualSaturationProcessNodeLinkerId {
        self.next
    }

    /// `CLinkerBase::setNext`.
    pub fn set_next(&mut self, next: IndividualSaturationProcessNodeLinkerId) -> &mut Self {
        self.next = next;
        self
    }
}
