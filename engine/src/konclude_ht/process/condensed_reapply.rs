//! `process::condensed_reapply` — the dynamic reapply queue head + descriptor
//! linker that feeds the (already-ported) `CCondensedReapplyQueueIterator`.
//!
//! Port of `Source/Reasoner/Kernel/Process/CCondensedReapplyQueue.{h,cpp}`.
//!
//! `CCondensedReapplyConceptDescriptor` (the chain element) and
//! `CCondensedReapplyQueueIterator` (the walker) are already ported in
//! `process::reapply_sat`; this unit ports the QUEUE that owns the head of the
//! `CCondensedReapplyConceptDescriptor*` linker chain and constructs that iterator.
//!
//! KONCLUDE-PORT-NOTE[ownership]: the C++ queue holds a raw
//! `CCondensedReapplyConceptDescriptor* mDynamicPosNegReapplyDesLinker` head; here
//! it is a `CondensedReapplyConceptDescriptorId` into
//! `ProcessContext::cond_reapply_con_descs`, and every `getNext()` /
//! `isPositiveDescriptor()` / `append(head)` deref threads `&ProcessContext` /
//! `&mut ProcessContext`. The optional reapply-count
//! (`KONCLUDE_EMPLOY_…_CONDENSED_REAPPLY_QUEUE_COUNT`) is compiled-out in the C++
//! build, so it is not modelled here.

#![allow(dead_code)]

use super::context::ProcessContext;
use super::reapply_sat::{CondensedReapplyConceptDescriptorId, CondensedReapplyQueueIterator};
use super::ConDescId;
use super::super::model::substrate::Id;

/// Port of `CCondensedReapplyQueue`.
///
/// Held BY VALUE inside the per-node label-set reapply-map values
/// (`ConceptDescriptorDependencyReapplyData::pos_neg_reapply_queue`,
/// `reapply_sat::LabelSetMapEntry::pos_neg_reapply_queue`), so it stays `Copy` +
/// `Clone` + `Default` like the C++ value member.
#[derive(Clone, Copy)]
pub struct CondensedReapplyQueue {
    /// `CCondensedReapplyConceptDescriptor* mDynamicPosNegReapplyDesLinker` (head).
    dynamic_pos_neg_reapply_des_linker: CondensedReapplyConceptDescriptorId,
}

impl Default for CondensedReapplyQueue {
    /// Port of `CCondensedReapplyQueue::CCondensedReapplyQueue()`
    /// (`mDynamicPosNegReapplyDesLinker = nullptr;`).
    fn default() -> Self {
        CondensedReapplyQueue {
            dynamic_pos_neg_reapply_des_linker: Id::NONE,
        }
    }
}

impl CondensedReapplyQueue {
    /// Port of the default ctor.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `initReapplyQueue(CCondensedReapplyQueue* prevReapplyQueue)`.
    /// KONCLUDE-PORT-NOTE[ownership]: the C++ `mDynamicPosNegReapplyDesLinker =
    /// prev->mDynamicPosNegReapplyDesLinker` shares the same chain head (the chain
    /// nodes live in the shared per-test pool); here both queues just hold the same
    /// `Id` into `cond_reapply_con_descs`.
    pub fn init_reapply_queue(&mut self, prev_reapply_queue: Option<&CondensedReapplyQueue>) -> &mut Self {
        if let Some(prev) = prev_reapply_queue {
            self.dynamic_pos_neg_reapply_des_linker = prev.dynamic_pos_neg_reapply_des_linker;
        } else {
            self.dynamic_pos_neg_reapply_des_linker = Id::NONE;
        }
        self
    }

    /// Port of `isEmpty` (`return !mDynamicPosNegReapplyDesLinker;`).
    pub fn is_empty(&self) -> bool {
        self.dynamic_pos_neg_reapply_des_linker.is_none()
    }

    /// The chain head (`mDynamicPosNegReapplyDesLinker`).
    pub fn dynamic_pos_neg_reapply_des_linker(&self) -> CondensedReapplyConceptDescriptorId {
        self.dynamic_pos_neg_reapply_des_linker
    }

    /// Port of `hasConceptDescriptor(CConceptDescriptor* conceptDescriptor)`.
    /// KONCLUDE-PORT-NOTE[pointer-alias]: the `desLinker->hasConceptDescriptor(cd)`
    /// (`getData() == cd`) + `desLinker->getNext()` derefs resolve against the
    /// descriptor arena, hence `&ProcessContext`.
    pub fn has_concept_descriptor(&self, ctx: &ProcessContext, concept_descriptor: ConDescId) -> bool {
        let mut des_linker = self.dynamic_pos_neg_reapply_des_linker;
        while des_linker.is_some() {
            let d = ctx.cond_reapply_con_desc(des_linker);
            if d.get_concept_descriptor() == concept_descriptor {
                return true;
            }
            des_linker = d.get_next();
        }
        false
    }

    /// Port of `addReapplyConceptDescriptor(CCondensedReapplyConceptDescriptor* conProDes)`.
    /// KONCLUDE-PORT-NOTE[ownership]: `conProDes->append(mDynamicPosNegReapplyDesLinker)`
    /// makes `conProDes` the new head and chains the existing head onto its `next`
    /// (head-front splice, PORT.md §6) — realised by setting the arena node's `next`.
    pub fn add_reapply_concept_descriptor(
        &mut self,
        ctx: &mut ProcessContext,
        con_pro_des: CondensedReapplyConceptDescriptorId,
    ) -> &mut Self {
        if con_pro_des.is_some() {
            ctx.cond_reapply_con_desc_mut(con_pro_des).next = self.dynamic_pos_neg_reapply_des_linker;
            self.dynamic_pos_neg_reapply_des_linker = con_pro_des;
        }
        self
    }

    /// Port of `getIterator(bool positiveDescriptors, bool negativeDescriptors, bool clearDynamicReapplyQueue)`.
    pub fn get_iterator(
        &mut self,
        ctx: &ProcessContext,
        positive_descriptors: bool,
        negative_descriptors: bool,
        clear_dynamic_reapply_queue: bool,
    ) -> CondensedReapplyQueueIterator {
        let it = CondensedReapplyQueueIterator::new_pos_neg(
            ctx,
            self.dynamic_pos_neg_reapply_des_linker,
            positive_descriptors,
            negative_descriptors,
        );
        if clear_dynamic_reapply_queue {
            self.dynamic_pos_neg_reapply_des_linker = Id::NONE;
        }
        it
    }

    /// Port of `getIterator(bool onlyPositiveDescriptors, bool clearDynamicReapplyQueue = true)`
    /// (`getIterator(only == true, only == false, clear)`).
    pub fn get_iterator_only_positive(
        &mut self,
        ctx: &ProcessContext,
        only_positive_descriptors: bool,
        clear_dynamic_reapply_queue: bool,
    ) -> CondensedReapplyQueueIterator {
        self.get_iterator(
            ctx,
            only_positive_descriptors,
            !only_positive_descriptors,
            clear_dynamic_reapply_queue,
        )
    }
}
