//! `process/db3.rs` — method-batch unit **DB-3**: the `CProcessingDataBox`
//! triple-buffered queue `get`/`clear` pairs (26 queues).
//!
//! Port of `Source/Reasoner/Kernel/Process/CProcessingDataBox.cpp` lines
//! 784–1284. Each logical queue slot is a triple `mX`/`mUseX`/`mPrevX` (kept as
//! the three plain `Id` fields on `ProcessingDataBox`, per the SD-2 ownership
//! note). The two methods per queue are:
//!
//!   * `getXxx(create)` — lazy-alloc getter: when the local handle is null and
//!     `create` is set, allocate the queue from the per-test pool, seed it from
//!     the saved `mPrevX` (`initProcessingQueue`), and publish it through `mUseX`;
//!     always return `mUseX`.
//!   * `clearXxx()` — null all three handles; returns `this`.
//!
//! QUEUE-PORT (un-defer): the C++ `getXxx` create branch allocates via
//! `CObjectParameterizingAllocator<…, CProcessContext*>` and calls
//! `initProcessingQueue(mPrevX)`. The port realises the per-test pool as the
//! `Arena<T>` fields on `ProcessContext` (the single pool every branch databox
//! shares — see `process::queues`), so the getters now take `ctx: &mut
//! ProcessContext` and call the matching `ctx.alloc_*_proc_queue_from_prev(prev)`
//! helper (allocate + `initProcessingQueue`). The `clear` bodies are exact.
//!
//! NOTE: `isBackendIndividualLateReuseExpansionActivated` (`.cpp` 905) and
//! `setBackendIndividualLateReuseExpansionActivated` (`.cpp` 909) fall inside this
//! `.cpp` range but are already ported in `databox.rs`, so they are skipped here.

#![allow(dead_code)]

use super::super::model::substrate::Id;
use super::context::ProcessContext;
use super::databox::ProcessingDataBox;
use super::stubs::{
    IndividualConceptBatchProcessingQueue, IndividualCustomPriorityProcessingQueue,
    IndividualDepthProcessingQueue, IndividualLinkerRotationProcessingQueue,
    IndividualUnsortedProcessingQueue,
};

impl ProcessingDataBox {
    /// Port of `CProcessingDataBox::getIndividualDepthFirstProcessingQueue`.
    /// `.cpp` 784–791.
    pub fn get_individual_depth_first_processing_queue(
        &mut self,
        ctx: &mut ProcessContext,
        create: bool,
    ) -> Id<IndividualUnsortedProcessingQueue> {
        if self.indi_depth_first_process_queue.is_none() && create {
            self.indi_depth_first_process_queue =
                ctx.alloc_unsorted_proc_queue_from_prev(self.prev_indi_depth_first_process_queue);
            self.use_indi_depth_first_process_queue = self.indi_depth_first_process_queue;
        }
        self.use_indi_depth_first_process_queue
    }

    /// Port of `CProcessingDataBox::clearIndividualDepthFirstProcessingQueue`.
    /// `.cpp` 794–799.
    pub fn clear_individual_depth_first_processing_queue(&mut self) -> &mut Self {
        self.indi_depth_first_process_queue = Id::NONE;
        self.use_indi_depth_first_process_queue = Id::NONE;
        self.prev_indi_depth_first_process_queue = Id::NONE;
        self
    }

    /// Port of `CProcessingDataBox::getIndividualImmediatelyProcessingQueue`.
    /// `.cpp` 803–810.
    pub fn get_individual_immediately_processing_queue(
        &mut self,
        ctx: &mut ProcessContext,
        create: bool,
    ) -> Id<IndividualUnsortedProcessingQueue> {
        if self.indi_imm_process_queue.is_none() && create {
            self.indi_imm_process_queue =
                ctx.alloc_unsorted_proc_queue_from_prev(self.prev_indi_imm_process_queue);
            self.use_indi_imm_process_queue = self.indi_imm_process_queue;
        }
        self.use_indi_imm_process_queue
    }

    /// Port of `CProcessingDataBox::clearIndividualImmediatelyProcessingQueue`.
    /// `.cpp` 813–818.
    pub fn clear_individual_immediately_processing_queue(&mut self) -> &mut Self {
        self.indi_imm_process_queue = Id::NONE;
        self.use_indi_imm_process_queue = Id::NONE;
        self.prev_indi_imm_process_queue = Id::NONE;
        self
    }

    /// Port of `CProcessingDataBox::getRoleAssertionExpansionProcessingQueue`.
    /// `.cpp` 822–829.
    pub fn get_role_assertion_expansion_processing_queue(
        &mut self,
        ctx: &mut ProcessContext,
        create: bool,
    ) -> Id<IndividualUnsortedProcessingQueue> {
        if self.role_assertion_process_queue.is_none() && create {
            self.role_assertion_process_queue =
                ctx.alloc_unsorted_proc_queue_from_prev(self.prev_role_assertion_process_queue);
            self.use_role_assertion_process_queue = self.role_assertion_process_queue;
        }
        self.use_role_assertion_process_queue
    }

    /// Port of `CProcessingDataBox::clearRoleAssertionProcessingQueue`.
    /// `.cpp` 832–837.
    pub fn clear_role_assertion_processing_queue(&mut self) -> &mut Self {
        self.role_assertion_process_queue = Id::NONE;
        self.use_role_assertion_process_queue = Id::NONE;
        self.prev_role_assertion_process_queue = Id::NONE;
        self
    }

    /// Port of `CProcessingDataBox::getBackendCacheSynchronizationProcessingQueue`.
    /// `.cpp` 842–849.
    pub fn get_backend_cache_synchronization_processing_queue(
        &mut self,
        ctx: &mut ProcessContext,
        create: bool,
    ) -> Id<IndividualUnsortedProcessingQueue> {
        if self.backend_sync_retest_process_queue.is_none() && create {
            self.backend_sync_retest_process_queue = ctx
                .alloc_unsorted_proc_queue_from_prev(self.prev_backend_sync_retest_process_queue);
            self.use_backend_sync_retest_process_queue = self.backend_sync_retest_process_queue;
        }
        self.use_backend_sync_retest_process_queue
    }

    /// Port of `CProcessingDataBox::clearBackendCacheSynchronizationProcessingQueue`.
    /// `.cpp` 852–857.
    pub fn clear_backend_cache_synchronization_processing_queue(&mut self) -> &mut Self {
        self.backend_sync_retest_process_queue = Id::NONE;
        self.use_backend_sync_retest_process_queue = Id::NONE;
        self.prev_backend_sync_retest_process_queue = Id::NONE;
        self
    }

    /// Port of `CProcessingDataBox::getBackendDirectInfluenceExpansionQueue`.
    /// `.cpp` 862–869.
    pub fn get_backend_direct_influence_expansion_queue(
        &mut self,
        ctx: &mut ProcessContext,
        create: bool,
    ) -> Id<IndividualUnsortedProcessingQueue> {
        if self.backend_direct_influence_expansion_queue.is_none() && create {
            self.backend_direct_influence_expansion_queue = ctx
                .alloc_unsorted_proc_queue_from_prev(
                    self.prev_backend_direct_influence_expansion_queue,
                );
            self.use_backend_direct_influence_expansion_queue =
                self.backend_direct_influence_expansion_queue;
        }
        self.use_backend_direct_influence_expansion_queue
    }

    /// Port of `CProcessingDataBox::clearBackendDirectInfluenceExpansionQueue`.
    /// `.cpp` 872–877.
    pub fn clear_backend_direct_influence_expansion_queue(&mut self) -> &mut Self {
        self.backend_direct_influence_expansion_queue = Id::NONE;
        self.use_backend_direct_influence_expansion_queue = Id::NONE;
        self.prev_backend_direct_influence_expansion_queue = Id::NONE;
        self
    }

    /// Port of `CProcessingDataBox::getBackendIndirectCompatibilityExpansionQueue`.
    /// `.cpp` 881–888.
    pub fn get_backend_indirect_compatibility_expansion_queue(
        &mut self,
        ctx: &mut ProcessContext,
        create: bool,
    ) -> Id<IndividualUnsortedProcessingQueue> {
        if self
            .backend_indirect_compatibility_expansion_queue
            .is_none()
            && create
        {
            self.backend_indirect_compatibility_expansion_queue = ctx
                .alloc_unsorted_proc_queue_from_prev(
                    self.prev_backend_indirect_compatibility_expansion_queue,
                );
            self.use_backend_indirect_compatibility_expansion_queue =
                self.backend_indirect_compatibility_expansion_queue;
        }
        self.use_backend_indirect_compatibility_expansion_queue
    }

    /// Port of `CProcessingDataBox::clearBackendIndirectCompatibilityExpansionQueue`.
    /// `.cpp` 891–896.
    pub fn clear_backend_indirect_compatibility_expansion_queue(&mut self) -> &mut Self {
        self.backend_indirect_compatibility_expansion_queue = Id::NONE;
        self.use_backend_indirect_compatibility_expansion_queue = Id::NONE;
        self.prev_backend_indirect_compatibility_expansion_queue = Id::NONE;
        self
    }

    // `.cpp` 905 isBackendIndividualLateReuseExpansionActivated and
    // `.cpp` 909 setBackendIndividualLateReuseExpansionActivated are ALREADY ported
    // in `databox.rs` (the simple getter/setter block) — skipped here.

    /// Port of `CProcessingDataBox::getBackendIndividualReuseExpansionQueue`.
    /// `.cpp` 916–923.
    ///
    /// KONCLUDE-PORT-NOTE[unclear]: the C++ method name says "ReuseExpansion" but
    /// the body operates the *late* reuse-expansion triple
    /// (`mBackendLateIndividualReuseExpansionQueue`/`mUse`/`mPrev`). Ported
    /// verbatim — the field choice matches the C++ exactly.
    pub fn get_backend_individual_reuse_expansion_queue(
        &mut self,
        ctx: &mut ProcessContext,
        create: bool,
    ) -> Id<IndividualUnsortedProcessingQueue> {
        if self.backend_late_individual_reuse_expansion_queue.is_none() && create {
            self.backend_late_individual_reuse_expansion_queue = ctx
                .alloc_unsorted_proc_queue_from_prev(
                    self.prev_backend_late_individual_reuse_expansion_queue,
                );
            self.use_backend_late_individual_reuse_expansion_queue =
                self.backend_late_individual_reuse_expansion_queue;
        }
        self.use_backend_late_individual_reuse_expansion_queue
    }

    /// Port of `CProcessingDataBox::clearBackendIndividualReuseExpansionQueue`.
    /// `.cpp` 926–931. (Clears the *late* reuse-expansion triple, matching the C++.)
    pub fn clear_backend_individual_reuse_expansion_queue(&mut self) -> &mut Self {
        self.backend_late_individual_reuse_expansion_queue = Id::NONE;
        self.use_backend_late_individual_reuse_expansion_queue = Id::NONE;
        self.prev_backend_late_individual_reuse_expansion_queue = Id::NONE;
        self
    }

    /// Port of `CProcessingDataBox::getBackendLateIndividualNeighbourExpansionQueue`.
    /// `.cpp` 940–947.
    ///
    /// KONCLUDE-PORT-NOTE[unclear]: the C++ method name says "Late...Neighbour" but
    /// the body operates the (non-late) reuse-expansion triple
    /// (`mBackendIndividualReuseExpansionQueue`/`mUse`/`mPrev`). Ported verbatim.
    pub fn get_backend_late_individual_neighbour_expansion_queue(
        &mut self,
        ctx: &mut ProcessContext,
        create: bool,
    ) -> Id<IndividualUnsortedProcessingQueue> {
        if self.backend_individual_reuse_expansion_queue.is_none() && create {
            self.backend_individual_reuse_expansion_queue = ctx
                .alloc_unsorted_proc_queue_from_prev(
                    self.prev_backend_individual_reuse_expansion_queue,
                );
            self.use_backend_individual_reuse_expansion_queue =
                self.backend_individual_reuse_expansion_queue;
        }
        self.use_backend_individual_reuse_expansion_queue
    }

    /// Port of `CProcessingDataBox::clearBackendLateIndividualNeighbourExpansionQueue`.
    /// `.cpp` 950–955. (Clears the non-late reuse-expansion triple, matching the C++.)
    pub fn clear_backend_late_individual_neighbour_expansion_queue(&mut self) -> &mut Self {
        self.backend_individual_reuse_expansion_queue = Id::NONE;
        self.use_backend_individual_reuse_expansion_queue = Id::NONE;
        self.prev_backend_individual_reuse_expansion_queue = Id::NONE;
        self
    }

    /// Port of `CProcessingDataBox::getBackendIndividualNeighbourExpansionQueue`.
    /// `.cpp` 969–976.
    pub fn get_backend_individual_neighbour_expansion_queue(
        &mut self,
        ctx: &mut ProcessContext,
        create: bool,
    ) -> Id<IndividualLinkerRotationProcessingQueue> {
        if self.backend_individual_neighbour_expansion_queue.is_none() && create {
            self.backend_individual_neighbour_expansion_queue = ctx
                .alloc_rotation_proc_queue_from_prev(
                    self.prev_backend_individual_neighbour_expansion_queue,
                );
            self.use_backend_individual_neighbour_expansion_queue =
                self.backend_individual_neighbour_expansion_queue;
        }
        self.use_backend_individual_neighbour_expansion_queue
    }

    /// Port of `CProcessingDataBox::clearBackendIndividualNeighbourExpansionQueue`.
    /// `.cpp` 979–984.
    pub fn clear_backend_individual_neighbour_expansion_queue(&mut self) -> &mut Self {
        self.backend_individual_neighbour_expansion_queue = Id::NONE;
        self.use_backend_individual_neighbour_expansion_queue = Id::NONE;
        self.prev_backend_individual_neighbour_expansion_queue = Id::NONE;
        self
    }

    /// Port of `CProcessingDataBox::getDelayingNominalProcessingQueue`.
    /// `.cpp` 990–997.
    pub fn get_delaying_nominal_processing_queue(
        &mut self,
        ctx: &mut ProcessContext,
        create: bool,
    ) -> Id<IndividualUnsortedProcessingQueue> {
        if self.delay_nom_process_queue.is_none() && create {
            self.delay_nom_process_queue =
                ctx.alloc_unsorted_proc_queue_from_prev(self.prev_delay_nom_process_queue);
            self.use_delay_nom_process_queue = self.delay_nom_process_queue;
        }
        self.use_delay_nom_process_queue
    }

    /// Port of `CProcessingDataBox::clearDelayingNominalProcessingQueue`.
    /// `.cpp` 1000–1005.
    pub fn clear_delaying_nominal_processing_queue(&mut self) -> &mut Self {
        self.delay_nom_process_queue = Id::NONE;
        self.use_delay_nom_process_queue = Id::NONE;
        self.prev_delay_nom_process_queue = Id::NONE;
        self
    }

    /// Port of `CProcessingDataBox::getNominalCachingLossReactivationProcessingQueue`.
    /// `.cpp` 1009–1016.
    pub fn get_nominal_caching_loss_reactivation_processing_queue(
        &mut self,
        ctx: &mut ProcessContext,
        create: bool,
    ) -> Id<IndividualUnsortedProcessingQueue> {
        if self.caching_loss_reactivation_process_queue.is_none() && create {
            self.caching_loss_reactivation_process_queue = ctx.alloc_unsorted_proc_queue_from_prev(
                self.prev_caching_loss_reactivation_process_queue,
            );
            self.use_caching_loss_reactivation_process_queue =
                self.caching_loss_reactivation_process_queue;
        }
        self.use_caching_loss_reactivation_process_queue
    }

    /// Port of `CProcessingDataBox::clearNominalCachingLossReactivationProcessingQueue`.
    /// `.cpp` 1019–1024.
    pub fn clear_nominal_caching_loss_reactivation_processing_queue(&mut self) -> &mut Self {
        self.caching_loss_reactivation_process_queue = Id::NONE;
        self.use_caching_loss_reactivation_process_queue = Id::NONE;
        self.prev_caching_loss_reactivation_process_queue = Id::NONE;
        self
    }

    /// Port of `CProcessingDataBox::getVariableBindingConceptBatchProcessingQueue`.
    /// `.cpp` 1027–1034.
    ///
    pub fn get_variable_binding_concept_batch_processing_queue(
        &mut self,
        ctx: &mut ProcessContext,
        create: bool,
    ) -> Id<IndividualConceptBatchProcessingQueue> {
        if self.var_bind_concept_batch_process_queue.is_none() && create {
            self.var_bind_concept_batch_process_queue = ctx
                .alloc_concept_batch_proc_queue_from_prev(
                    self.prev_var_bind_concept_batch_process_queue,
                );
            self.use_var_bind_concept_batch_process_queue =
                self.var_bind_concept_batch_process_queue;
        }
        self.use_var_bind_concept_batch_process_queue
    }

    /// Port of `CProcessingDataBox::clearVariableBindingConceptBatchProcessingQueue`.
    /// `.cpp` 1036–1041.
    pub fn clear_variable_binding_concept_batch_processing_queue(&mut self) -> &mut Self {
        self.var_bind_concept_batch_process_queue = Id::NONE;
        self.use_var_bind_concept_batch_process_queue = Id::NONE;
        self.prev_var_bind_concept_batch_process_queue = Id::NONE;
        self
    }

    /// Port of `CProcessingDataBox::getIndividualDepthProcessingQueue`.
    /// `.cpp` 1045–1052.
    pub fn get_individual_depth_processing_queue(
        &mut self,
        ctx: &mut ProcessContext,
        create: bool,
    ) -> Id<IndividualDepthProcessingQueue> {
        if self.indi_depth_processing_queue.is_none() && create {
            self.indi_depth_processing_queue =
                ctx.alloc_depth_proc_queue_from_prev(self.prev_indi_depth_processing_queue);
            self.use_indi_depth_processing_queue = self.indi_depth_processing_queue;
        }
        self.use_indi_depth_processing_queue
    }

    /// Port of `CProcessingDataBox::clearIndividualDepthProcessingQueue`.
    /// `.cpp` 1055–1060.
    pub fn clear_individual_depth_processing_queue(&mut self) -> &mut Self {
        self.indi_depth_processing_queue = Id::NONE;
        self.use_indi_depth_processing_queue = Id::NONE;
        self.prev_indi_depth_processing_queue = Id::NONE;
        self
    }

    /// Port of `CProcessingDataBox::getNominalDeterministicProcessingQueue`.
    /// `.cpp` 1068–1075.
    pub fn get_nominal_deterministic_processing_queue(
        &mut self,
        ctx: &mut ProcessContext,
        create: bool,
    ) -> Id<IndividualDepthProcessingQueue> {
        if self.nominal_deterministic_processing_queue.is_none() && create {
            self.nominal_deterministic_processing_queue = ctx
                .alloc_depth_proc_queue_from_prev(self.prev_nominal_deterministic_processing_queue);
            self.use_nominal_deterministic_processing_queue =
                self.nominal_deterministic_processing_queue;
        }
        self.use_nominal_deterministic_processing_queue
    }

    /// Port of `CProcessingDataBox::clearNominalDeterministicProcessingQueue`.
    /// `.cpp` 1078–1083.
    pub fn clear_nominal_deterministic_processing_queue(&mut self) -> &mut Self {
        self.nominal_deterministic_processing_queue = Id::NONE;
        self.use_nominal_deterministic_processing_queue = Id::NONE;
        self.prev_nominal_deterministic_processing_queue = Id::NONE;
        self
    }

    /// Port of `CProcessingDataBox::getNominalProcessingQueue`.
    /// `.cpp` 1088–1095.
    pub fn get_nominal_processing_queue(
        &mut self,
        ctx: &mut ProcessContext,
        create: bool,
    ) -> Id<IndividualDepthProcessingQueue> {
        if self.nominal_processing_queue.is_none() && create {
            self.nominal_processing_queue =
                ctx.alloc_depth_proc_queue_from_prev(self.prev_nominal_processing_queue);
            self.use_nominal_processing_queue = self.nominal_processing_queue;
        }
        self.use_nominal_processing_queue
    }

    /// Port of `CProcessingDataBox::clearNominalProcessingQueue`.
    /// `.cpp` 1098–1103.
    pub fn clear_nominal_processing_queue(&mut self) -> &mut Self {
        self.nominal_processing_queue = Id::NONE;
        self.use_nominal_processing_queue = Id::NONE;
        self.prev_nominal_processing_queue = Id::NONE;
        self
    }

    /// Port of `CProcessingDataBox::getIncrementalExpansionInitializingProcessingQueue`.
    /// `.cpp` 1110–1117.
    pub fn get_incremental_expansion_initializing_processing_queue(
        &mut self,
        ctx: &mut ProcessContext,
        create: bool,
    ) -> Id<IndividualDepthProcessingQueue> {
        if self
            .incremental_exansion_initializing_processing_queue
            .is_none()
            && create
        {
            self.incremental_exansion_initializing_processing_queue = ctx
                .alloc_depth_proc_queue_from_prev(
                    self.prev_incremental_exansion_initializing_processing_queue,
                );
            self.use_incremental_exansion_initializing_processing_queue =
                self.incremental_exansion_initializing_processing_queue;
        }
        self.use_incremental_exansion_initializing_processing_queue
    }

    /// Port of `CProcessingDataBox::clearIncrementalExpansionInitializingProcessingQueue`.
    /// `.cpp` 1120–1125.
    pub fn clear_incremental_expansion_initializing_processing_queue(&mut self) -> &mut Self {
        self.incremental_exansion_initializing_processing_queue = Id::NONE;
        self.use_incremental_exansion_initializing_processing_queue = Id::NONE;
        self.prev_incremental_exansion_initializing_processing_queue = Id::NONE;
        self
    }

    /// Port of `CProcessingDataBox::getIncrementalExpansionProcessingQueue`.
    /// `.cpp` 1131–1138.
    ///
    pub fn get_incremental_expansion_processing_queue(
        &mut self,
        ctx: &mut ProcessContext,
        create: bool,
    ) -> Id<IndividualCustomPriorityProcessingQueue> {
        if self.incremental_exansion_processing_queue.is_none() && create {
            self.incremental_exansion_processing_queue = ctx
                .alloc_custom_priority_proc_queue_from_prev(
                    self.prev_incremental_exansion_processing_queue,
                );
            self.use_incremental_exansion_processing_queue =
                self.incremental_exansion_processing_queue;
        }
        self.use_incremental_exansion_processing_queue
    }

    /// Port of `CProcessingDataBox::clearIncrementalExpansionIProcessingQueue`.
    /// `.cpp` 1141–1146. (Name carries the C++ "I" typo verbatim.)
    pub fn clear_incremental_expansion_i_processing_queue(&mut self) -> &mut Self {
        self.incremental_exansion_processing_queue = Id::NONE;
        self.use_incremental_exansion_processing_queue = Id::NONE;
        self.prev_incremental_exansion_processing_queue = Id::NONE;
        self
    }

    /// Port of `CProcessingDataBox::getIncrementalCompatibilityCheckingQueue`.
    /// `.cpp` 1152–1159.
    pub fn get_incremental_compatibility_checking_queue(
        &mut self,
        ctx: &mut ProcessContext,
        create: bool,
    ) -> Id<IndividualDepthProcessingQueue> {
        if self.incremental_compatibility_checking_queue.is_none() && create {
            self.incremental_compatibility_checking_queue = ctx.alloc_depth_proc_queue_from_prev(
                self.prev_incremental_compatibility_checking_queue,
            );
            self.use_incremental_compatibility_checking_queue =
                self.incremental_compatibility_checking_queue;
        }
        self.use_incremental_compatibility_checking_queue
    }

    /// Port of `CProcessingDataBox::clearIncrementalCompatibilityCheckingQueue`.
    /// `.cpp` 1162–1167.
    pub fn clear_incremental_compatibility_checking_queue(&mut self) -> &mut Self {
        self.incremental_compatibility_checking_queue = Id::NONE;
        self.use_incremental_compatibility_checking_queue = Id::NONE;
        self.prev_incremental_compatibility_checking_queue = Id::NONE;
        self
    }

    /// Port of `CProcessingDataBox::getIndividualDepthFirstDeterministicExpansionProcessingQueue`.
    /// `.cpp` 1172–1179.
    pub fn get_individual_depth_first_deterministic_expansion_processing_queue(
        &mut self,
        ctx: &mut ProcessContext,
        create: bool,
    ) -> Id<IndividualUnsortedProcessingQueue> {
        if self.indi_depth_first_det_exp_pre_processing_queue.is_none() && create {
            self.indi_depth_first_det_exp_pre_processing_queue = ctx
                .alloc_unsorted_proc_queue_from_prev(
                    self.prev_indi_depth_first_det_exp_pre_processing_queue,
                );
            self.use_indi_depth_first_det_exp_pre_processing_queue =
                self.indi_depth_first_det_exp_pre_processing_queue;
        }
        self.use_indi_depth_first_det_exp_pre_processing_queue
    }

    /// Port of `CProcessingDataBox::clearIndividualDepthFirstDeterministicExpansionProcessingQueue`.
    /// `.cpp` 1181–1186.
    pub fn clear_individual_depth_first_deterministic_expansion_processing_queue(
        &mut self,
    ) -> &mut Self {
        self.indi_depth_first_det_exp_pre_processing_queue = Id::NONE;
        self.use_indi_depth_first_det_exp_pre_processing_queue = Id::NONE;
        self.prev_indi_depth_first_det_exp_pre_processing_queue = Id::NONE;
        self
    }

    /// Port of `CProcessingDataBox::getIndividualDepthDeterministicExpansionPreprocessingQueue`.
    /// `.cpp` 1190–1197.
    pub fn get_individual_depth_deterministic_expansion_preprocessing_queue(
        &mut self,
        ctx: &mut ProcessContext,
        create: bool,
    ) -> Id<IndividualDepthProcessingQueue> {
        if self.indi_depth_det_exp_pre_processing_queue.is_none() && create {
            self.indi_depth_det_exp_pre_processing_queue = ctx.alloc_depth_proc_queue_from_prev(
                self.prev_indi_depth_det_exp_pre_processing_queue,
            );
            self.use_indi_depth_det_exp_pre_processing_queue =
                self.indi_depth_det_exp_pre_processing_queue;
        }
        self.use_indi_depth_det_exp_pre_processing_queue
    }

    /// Port of `CProcessingDataBox::clearIndividualDepthDeterministicExpansionPreprocessingQueue`.
    /// `.cpp` 1200–1205.
    pub fn clear_individual_depth_deterministic_expansion_preprocessing_queue(
        &mut self,
    ) -> &mut Self {
        self.indi_depth_det_exp_pre_processing_queue = Id::NONE;
        self.use_indi_depth_det_exp_pre_processing_queue = Id::NONE;
        self.prev_indi_depth_det_exp_pre_processing_queue = Id::NONE;
        self
    }

    /// Port of `CProcessingDataBox::getBlockingUpdateReviewProcessingQueue`.
    /// `.cpp` 1209–1216.
    pub fn get_blocking_update_review_processing_queue(
        &mut self,
        ctx: &mut ProcessContext,
        create: bool,
    ) -> Id<IndividualDepthProcessingQueue> {
        if self
            .indi_signature_blocking_update_processing_queue
            .is_none()
            && create
        {
            self.indi_signature_blocking_update_processing_queue = ctx
                .alloc_depth_proc_queue_from_prev(
                    self.prev_indi_signature_blocking_update_processing_queue,
                );
            self.use_indi_signature_blocking_update_processing_queue =
                self.indi_signature_blocking_update_processing_queue;
        }
        self.use_indi_signature_blocking_update_processing_queue
    }

    /// Port of `CProcessingDataBox::clearBlockingUpdateReviewProcessingQueue`.
    /// `.cpp` 1219–1224.
    pub fn clear_blocking_update_review_processing_queue(&mut self) -> &mut Self {
        self.indi_signature_blocking_update_processing_queue = Id::NONE;
        self.use_indi_signature_blocking_update_processing_queue = Id::NONE;
        self.prev_indi_signature_blocking_update_processing_queue = Id::NONE;
        self
    }

    /// Port of `CProcessingDataBox::getBlockedReactivationProcessingQueue`.
    /// `.cpp` 1227–1234.
    pub fn get_blocked_reactivation_processing_queue(
        &mut self,
        ctx: &mut ProcessContext,
        create: bool,
    ) -> Id<IndividualDepthProcessingQueue> {
        if self.indi_blocked_reactivation_processing_queue.is_none() && create {
            self.indi_blocked_reactivation_processing_queue = ctx.alloc_depth_proc_queue_from_prev(
                self.prev_indi_blocked_reactivation_processing_queue,
            );
            self.use_indi_blocked_reactivation_processing_queue =
                self.indi_blocked_reactivation_processing_queue;
        }
        self.use_indi_blocked_reactivation_processing_queue
    }

    /// Port of `CProcessingDataBox::clearBlockedReactivationProcessingQueue`.
    /// `.cpp` 1237–1242.
    pub fn clear_blocked_reactivation_processing_queue(&mut self) -> &mut Self {
        self.indi_blocked_reactivation_processing_queue = Id::NONE;
        self.use_indi_blocked_reactivation_processing_queue = Id::NONE;
        self.prev_indi_blocked_reactivation_processing_queue = Id::NONE;
        self
    }

    /// Port of `CProcessingDataBox::getValueSpaceTriggeringProcessingQueue`.
    /// `.cpp` 1247–1254.
    pub fn get_value_space_triggering_processing_queue(
        &mut self,
        ctx: &mut ProcessContext,
        create: bool,
    ) -> Id<IndividualDepthProcessingQueue> {
        if self.value_space_triggering_processing_queue.is_none() && create {
            self.value_space_triggering_processing_queue = ctx.alloc_depth_proc_queue_from_prev(
                self.prev_value_space_triggering_processing_queue,
            );
            self.use_value_space_triggering_processing_queue =
                self.value_space_triggering_processing_queue;
        }
        self.use_value_space_triggering_processing_queue
    }

    /// Port of `CProcessingDataBox::clearValueSpaceTriggeringProcessingQueue`.
    /// `.cpp` 1257–1262.
    pub fn clear_value_space_triggering_processing_queue(&mut self) -> &mut Self {
        self.value_space_triggering_processing_queue = Id::NONE;
        self.use_value_space_triggering_processing_queue = Id::NONE;
        self.prev_value_space_triggering_processing_queue = Id::NONE;
        self
    }

    /// Port of `CProcessingDataBox::getDistinctValueSpaceSatisfiabilityCheckingQueue`.
    /// `.cpp` 1269–1276.
    pub fn get_distinct_value_space_satisfiability_checking_queue(
        &mut self,
        ctx: &mut ProcessContext,
        create: bool,
    ) -> Id<IndividualDepthProcessingQueue> {
        if self
            .distinct_value_space_satisfiability_checking_queue
            .is_none()
            && create
        {
            self.distinct_value_space_satisfiability_checking_queue = ctx
                .alloc_depth_proc_queue_from_prev(
                    self.prev_distinct_value_space_satisfiability_checking_queue,
                );
            self.use_distinct_value_space_satisfiability_checking_queue =
                self.distinct_value_space_satisfiability_checking_queue;
        }
        self.use_distinct_value_space_satisfiability_checking_queue
    }

    /// Port of `CProcessingDataBox::clearDistinctValueSpaceSatisfiabilityCheckingQueue`.
    /// `.cpp` 1279–1284.
    pub fn clear_distinct_value_space_satisfiability_checking_queue(&mut self) -> &mut Self {
        self.distinct_value_space_satisfiability_checking_queue = Id::NONE;
        self.use_distinct_value_space_satisfiability_checking_queue = Id::NONE;
        self.prev_distinct_value_space_satisfiability_checking_queue = Id::NONE;
        self
    }
}
