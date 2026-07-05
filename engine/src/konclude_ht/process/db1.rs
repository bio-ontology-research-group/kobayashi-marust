//! `process/db1.rs` — method-batch unit **DB-1**: the `CProcessingDataBox`
//! lifecycle / save-restore methods.
//!
//! Port of `Source/Reasoner/Kernel/Process/CProcessingDataBox.cpp` lines 33–541
//! (the constructor + `initProcessingDataBox(CConcreteOntology*)` +
//! `setProcessingOntology` + `initProcessingDataBox(CProcessingDataBox*)`). These
//! are ported FIRST because the parent→child handoff in
//! `init_processing_data_box_parent` is what defines, for every later DB unit,
//! which buffered slot is copied, which is nulled, and how the
//! `mX`/`mUseX`/`mPrevX` triple-buffer save/restore works.
//!
//! KONCLUDE-PORT-NOTE[ownership]: Konclude's intrusive `CLinker`/`CXLinker` chain
//! heads are shared by raw pointer in the parent handoff (parent and child alias
//! the same chain, which the pool/branch structure keeps coherent). The port owns
//! each chain as a `Vec`, so "copy the head pointer" becomes `.clone()` and
//! "= nullptr" becomes `.clear()`. This is the single global substrate decision
//! (`model/substrate.rs`); behaviour is identical for the read-only handoff, only
//! the representation differs.
//!
//! KONCLUDE-PORT-NOTE[overload]: C++ has two `initProcessingDataBox` overloads
//! (by `CConcreteOntology*` vs `CProcessingDataBox*`); Rust has no overloading, so
//! they are split into `init_processing_data_box_ontology` and
//! `init_processing_data_box_parent`.

#![allow(dead_code)]

use super::super::model::substrate::{Cint64, Id, INVALID};
use super::super::model::ConceptId;
use super::context::ProcessContext;
use super::databox::ProcessingDataBox;
use super::node_resolution::IndividualProcessNodeVector;
use super::stubs::{ConceptVector, IndividualVector};

impl ProcessingDataBox {
    /// Port of `CProcessingDataBox::CProcessingDataBox`.
    ///
    /// KONCLUDE-PORT-NOTE[uninit]: the C++ ctor assigns the great majority of its
    /// members to `nullptr`/`0`/`false`; `ProcessingDataBox::new` (databax.rs)
    /// already supplies exactly that null base (it was designated the `[uninit]`
    /// placeholder this unit fills). Here we build on it and apply only the ctor's
    /// distinctive non-default seeds, in C++ source order, so the two trees diff
    /// cleanly.
    pub fn with_process_context(process_context: Cint64) -> Self {
        let mut b = Self::new();
        // `.cpp` 33: mProcessContext(processContext)
        b.process_context = process_context;
        // `.cpp` 34: mIndiProcessVector = allocate CIndividualProcessNodeVector.
        // The port stores `mIndiProcessVector` by value; `ProcessingDataBox::new`
        // already constructs the empty vector that C++ allocates from the process
        // context pool.
        // `.cpp` 141: mNextSatResSuccExtIndividualNodeID = -1
        b.next_sat_res_succ_ext_individual_node_id = -1;
        // `.cpp` 142: mNextPropagationID = 1
        b.next_propagation_id = 1;
        // `.cpp` 143: mNextVariableID = 1
        b.next_variable_id = 1;
        // `.cpp` 144: mNextRepVariableID = 1
        b.next_rep_variable_id = 1;
        // `.cpp` 244: mNextIncrementalIndiExpID = 1
        b.next_incremental_indi_exp_id = 1;
        // `.cpp` 245: mNextRoleAssertionCreationID = 1
        b.next_role_assertion_creation_id = 1;
        // `.cpp` 251: mRemainingPossibleInstanceIndividualMergingLimit = -1
        b.remaining_possible_instance_individual_merging_limit = -1;
        // `.cpp` 252: mPossibleInstanceIndividualMergingSize = 1
        b.possible_instance_individual_merging_size = 1;
        b
    }

    /// Port of `CProcessingDataBox::initProcessingDataBox(CConcreteOntology*)`.
    /// `.cpp` 268–275.
    pub fn init_processing_data_box_ontology(&mut self, ontology: Cint64) -> &mut Self {
        // KONCLUDE-PORT-NOTE[api]: `CConcreteOntology` is still opaque in this
        // layer, so this compatibility entry point cannot dereference TBox/ABox.
        // `init_processing_data_box_ontology_resolved` below is the exact port
        // target once the caller has the four getter results.
        self.init_processing_data_box_ontology_resolved(
            ontology,
            ConceptId::NONE,
            ConceptId::NONE,
            Id::NONE,
            Id::NONE,
        )
    }

    /// Port-facing resolved form of
    /// `CProcessingDataBox::initProcessingDataBox(CConcreteOntology*)`.
    ///
    /// The C++ body dereferences `ontology` immediately:
    /// `.cpp` 269–273 assign `mOntology`, `mOntologyTopConcept`,
    /// `mOntologyTopDataRangeConcept`, `mUseExtendedConceptVector`, and
    /// `mUseIndiVector`. The current Rust layer still carries
    /// `CConcreteOntology*` as an opaque `Cint64`, so this method receives the
    /// four already-resolved getter results and performs the exact DB-1 field
    /// updates without manufacturing ids.
    pub fn init_processing_data_box_ontology_resolved(
        &mut self,
        ontology: Cint64,
        top_concept: ConceptId,
        top_data_range_concept: ConceptId,
        concept_vector: Id<ConceptVector>,
        individual_vector: Id<IndividualVector>,
    ) -> &mut Self {
        // `.cpp` 269: mOntology = ontology;
        self.ontology = ontology;
        // `.cpp` 270: mOntologyTopConcept = mOntology->getTBox()->getTopConcept();
        self.ontology_top_concept = top_concept;
        // `.cpp` 271: mOntologyTopDataRangeConcept =
        //   mOntology->getTBox()->getTopDataRangeConcept();
        self.ontology_top_data_range_concept = top_data_range_concept;
        // `.cpp` 272: mUseExtendedConceptVector =
        //   mOntology->getTBox()->getConceptVector(false);
        self.use_extended_concept_vector = concept_vector;
        // `.cpp` 273: mUseIndiVector =
        //   mOntology->getABox()->getIndividualVector(false);
        self.use_indi_vector = individual_vector;
        self
    }

    /// Port of `CProcessingDataBox::setProcessingOntology`. `.cpp` 278–281.
    pub fn set_processing_ontology(&mut self, ontology: Cint64) -> &mut Self {
        // `.cpp` 279: mOntology = ontology;
        self.ontology = ontology;
        self
    }

    /// Port of `CProcessingDataBox::initProcessingDataBox(CProcessingDataBox*)`.
    /// `.cpp` 284–541 — the parent→child triple-buffer save/restore handoff.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: the C++ takes a raw `CProcessingDataBox*`
    /// that may be `nullptr` (re-init without a parent); ported as
    /// `Option<&ProcessingDataBox>`. The reset block (`.cpp` 286–369) runs
    /// unconditionally; the copy block (`.cpp` 370–538) runs only when a parent is
    /// present.
    pub fn init_processing_data_box_parent(
        &mut self,
        parent: Option<&ProcessingDataBox>,
    ) -> &mut Self {
        self.init_processing_data_box_parent_internal(parent, None)
    }

    /// Context-threaded port of
    /// `CProcessingDataBox::initProcessingDataBox(CProcessingDataBox*)`.
    ///
    /// Konclude allocates DB-5 saturation satellites from `mProcessContext` when
    /// the parent owns one, then initializes the child satellite from the parent
    /// object. Rust keeps those satellites in `ProcessContext` arenas, so this
    /// entry point is the exact parent-copy path for arena-backed satellites.
    pub fn init_processing_data_box_parent_with_process_context(
        &mut self,
        parent: Option<&ProcessingDataBox>,
        process_context: &mut ProcessContext,
    ) -> &mut Self {
        self.init_processing_data_box_parent_internal(parent, Some(process_context))
    }

    fn init_processing_data_box_parent_internal(
        &mut self,
        parent: Option<&ProcessingDataBox>,
        mut process_context: Option<&mut ProcessContext>,
    ) -> &mut Self {
        // `.cpp` 285: CIndividualProcessNodeVector* prevIndiProcVec = nullptr;
        // KONCLUDE-PORT-NOTE[ownership]: the node vector is now a real ported type held
        // BY VALUE on the databox (node-resolution keystone); this save-local captures a
        // clone of the parent's, preserving the existing (deferred) save/restore body.
        let mut prev_indi_proc_vec: IndividualProcessNodeVector =
            IndividualProcessNodeVector::new();

        // --- unconditional reset (`.cpp` 286–369) ---
        self.use_indi_process_queue = Id::NONE; // 286
        self.loc_indi_process_queue = Id::NONE; // 287
        self.ontology = INVALID; // 288  (mOntology = nullptr)
        self.individual_node_cache_testing_linker.clear(); // 289
        self.sorted_nominal_non_det_processing_node_linker.clear(); // 290
        self.sorted_nominal_non_det_processing_nodes_sorted = false; // 291
        self.nominal_non_det_processing_count = 0; // 292
        self.individual_node_resolve_linker.clear(); // 293
        self.blockable_individual_node_updated_linker.clear(); // 294
        self.last_con_des_indi_reapplication = false; // 295
        self.indi_process_node_linker = Id::NONE; // 296
        self.rem_sat_update_linker.clear(); // 297
        self.rem_sat_indi_node_linker.clear(); // 298
        self.rem_sat_indi_succ_link_data_linker = Id::NONE; // 299
        self.rem_con_sat_des.clear(); // 300
        self.rem_con_des.clear(); // 301
        self.rem_role_sat_process_linker.clear(); // 302

        self.indi_saturation_process_node_linker.clear(); // 304
        self.indi_saturation_completion_node_linker.clear(); // 305
        self.indi_saturation_completed_node_linker.clear(); // 306
        self.indi_saturation_analysing_node_linker.clear(); // 307
        self.saturation_atmost_merging_process_linker = Id::NONE; // 308
        self.nominal_delayed_indi_saturation_process_node_linker
            .clear(); // 309
        self.disjunct_common_concept_extract_processing_linker
            .clear(); // 310
        self.rem_con_sat_process_linker.clear(); // 311
        self.indi_saturation_process_vector = None; // 312
        self.sat_critical_indi_node_proc_queue = Id::NONE; // 313
        self.sat_succ_ext_ind_node_proc_queue = Id::NONE; // 314
        self.sat_critical_indi_node_con_test_set = Id::NONE; // 315
        self.sat_nominal_dependent_node_hash = Id::NONE; // 316
        self.sat_influenced_nominal_set = Id::NONE; // 317
        self.constructed_indi_node_initialized = false; // 318
        self.multiple_construction_indi_nodes = false; // 319
        self.loc_extended_concept_vector = Id::NONE; // 320
        self.use_extended_concept_vector = Id::NONE; // 321
        self.use_grounding_hash = Id::NONE; // 322
        self.loc_grounding_hash = Id::NONE; // 323
        self.loc_var_binding_path_merging_hash = Id::NONE; // 324
        self.use_var_binding_path_merging_hash = Id::NONE; // 325
        self.loc_rep_var_bind_path_set_hash = Id::NONE; // 326
        self.use_rep_var_bind_path_set_hash = Id::NONE; // 327
        self.loc_rep_var_bind_path_hash = Id::NONE; // 328
        self.use_rep_var_bind_path_hash = Id::NONE; // 329
        self.loc_rep_var_bind_path_joining_key_hash = Id::NONE; // 330
        self.use_rep_var_bind_path_joining_key_hash = Id::NONE; // 331
        self.loc_rep_joining_hash = Id::NONE; // 332
        self.use_rep_joining_hash = Id::NONE; // 333
        self.loc_nom_caching_loss_react_hash = Id::NONE; // 334
        self.use_nom_caching_loss_react_hash = Id::NONE; // 335
        self.use_marker_indi_node_hash = Id::NONE; // 336
        self.loc_marker_indi_node_hash = Id::NONE; // 337
        self.use_backend_loaded_association_hash = Id::NONE; // 338
        self.loc_backend_loaded_association_hash = Id::NONE; // 339
        self.use_backend_concept_set_label_processing_hash = Id::NONE; // 340
        self.loc_backend_concept_set_label_processing_hash = Id::NONE; // 341
        self.use_backend_neighbour_expansion_controlling_data = Id::NONE; // 342
        self.loc_backend_neighbour_expansion_controlling_data = Id::NONE; // 343
        self.next_individual_node_id = 0; // 344
        self.next_sat_res_succ_ext_individual_node_id = -1; // 345
        self.next_propagation_id = 1; // 346
        self.next_variable_id = 1; // 347
        self.next_rep_variable_id = 1; // 348
        self.insufficient_node_occured = false; // 349
        self.delayed_nominal_processing_occured = false; // 350
        self.problematic_eq_candidate_node_occured = false; // 351
        self.incremental_expansion_initialized = false; // 352
        self.incremental_expansion_compatible_merged = false; // 353
        self.incremental_expansion_caching_merged = false; // 354
        self.separated_saturation_con_ass_resolve_node = Id::NONE; // 355
        self.branching_instruction = Id::NONE; // 356
        self.remaining_possible_instance_individual_merging_limit = -1; // 357
        self.possible_instance_individual_merging_stopped = false; // 358
        self.possible_instance_individual_merging_size = 1; // 359
        self.possible_instance_individual_merged_count = 0; // 360
        self.possible_instance_individual_current_merging_count = 0; // 361
        self.last_merged_possible_instance_individual_linker.clear(); // 362
        self.current_merged_possible_instance_individual_linkers_linker
            .clear(); // 363
        self.last_backend_cache_integrated_indi_node_linker.clear(); // 364
        self.backend_cache_integrated_individual_node_count = 0; // 365
        self.backend_cache_integrated_same_individual_node_count = 0; // 366
        self.local_indi_vector = Id::NONE; // 367
        self.backend_cache_update_individuals_initialized = false; // 368
        self.representative_neighbour_expansion_individual_node_linker
            .clear(); // 369

        // --- copy block: parent → child (`.cpp` 370–538) ---
        if let Some(parent) = parent {
            self.possible_instance_individual_merging_stopped =
                parent.possible_instance_individual_merging_stopped; // 371
            self.possible_instance_individual_merging_size =
                parent.possible_instance_individual_merging_size; // 372
            self.possible_instance_individual_merged_count =
                parent.possible_instance_individual_merged_count; // 373
            self.possible_instance_individual_current_merging_count =
                parent.possible_instance_individual_current_merging_count; // 374
            self.remaining_possible_instance_individual_merging_limit =
                parent.remaining_possible_instance_individual_merging_limit; // 375
            self.last_merged_possible_instance_individual_linker = parent
                .last_merged_possible_instance_individual_linker
                .clone(); // 376
            self.current_merged_possible_instance_individual_linkers_linker = parent
                .current_merged_possible_instance_individual_linkers_linker
                .clone(); // 377
            self.last_backend_cache_integrated_indi_node_linker = parent
                .last_backend_cache_integrated_indi_node_linker
                .clone(); // 378
            self.backend_cache_integrated_individual_node_count =
                parent.backend_cache_integrated_individual_node_count; // 379
            self.backend_cache_integrated_same_individual_node_count =
                parent.backend_cache_integrated_same_individual_node_count; // 380
            self.branching_instruction = parent.branching_instruction; // 381
            self.use_indi_process_queue = parent.use_indi_process_queue; // 382
            prev_indi_proc_vec = parent.indi_process_vector.clone(); // 383
            self.ontology = parent.ontology; // 384

            // triple-buffer restore: mPrevX = parent.mUseX; mUseX = mPrevX;
            self.prev_indi_depth_processing_queue = parent.use_indi_depth_processing_queue; // 385
            self.use_indi_depth_processing_queue = self.prev_indi_depth_processing_queue; // 386
            self.prev_nominal_processing_queue = parent.use_nominal_processing_queue; // 387
            self.use_nominal_processing_queue = self.prev_nominal_processing_queue; // 388
            self.prev_incremental_exansion_initializing_processing_queue =
                parent.use_incremental_exansion_initializing_processing_queue; // 389
            self.use_incremental_exansion_initializing_processing_queue =
                self.prev_incremental_exansion_initializing_processing_queue; // 390
            self.prev_incremental_compatibility_checking_queue =
                parent.use_incremental_compatibility_checking_queue; // 391
            self.use_incremental_compatibility_checking_queue =
                self.prev_incremental_compatibility_checking_queue; // 392
            self.prev_indi_depth_det_exp_pre_processing_queue =
                parent.use_indi_depth_det_exp_pre_processing_queue; // 393
            self.use_indi_depth_det_exp_pre_processing_queue =
                self.prev_indi_depth_det_exp_pre_processing_queue; // 394
            self.prev_indi_depth_first_det_exp_pre_processing_queue =
                parent.use_indi_depth_first_det_exp_pre_processing_queue; // 395
            self.use_indi_depth_first_det_exp_pre_processing_queue =
                self.prev_indi_depth_first_det_exp_pre_processing_queue; // 396
            self.prev_indi_blocked_reactivation_processing_queue =
                parent.use_indi_blocked_reactivation_processing_queue; // 397
            self.use_indi_blocked_reactivation_processing_queue =
                self.prev_indi_blocked_reactivation_processing_queue; // 398
            self.prev_var_bind_concept_batch_process_queue =
                parent.use_var_bind_concept_batch_process_queue; // 399
            self.use_var_bind_concept_batch_process_queue =
                self.prev_var_bind_concept_batch_process_queue; // 400
            self.prev_indi_signature_blocking_update_processing_queue =
                parent.use_indi_signature_blocking_update_processing_queue; // 401
            self.use_indi_signature_blocking_update_processing_queue =
                self.prev_indi_signature_blocking_update_processing_queue; // 402
            self.prev_value_space_triggering_processing_queue =
                parent.use_value_space_triggering_processing_queue; // 403
            self.use_value_space_triggering_processing_queue =
                self.prev_value_space_triggering_processing_queue; // 404
            self.prev_distinct_value_space_satisfiability_checking_queue =
                parent.use_distinct_value_space_satisfiability_checking_queue; // 405
            self.use_distinct_value_space_satisfiability_checking_queue =
                self.prev_distinct_value_space_satisfiability_checking_queue; // 406
            self.prev_signature_blocking_candidate_hash =
                parent.use_signature_blocking_candidate_hash; // 407
            self.use_signature_blocking_candidate_hash =
                self.prev_signature_blocking_candidate_hash; // 408

            self.prev_signature_nominal_delaying_candidate_hash =
                parent.use_signature_nominal_delaying_candidate_hash; // 410
            self.use_signature_nominal_delaying_candidate_hash =
                self.prev_signature_nominal_delaying_candidate_hash; // 411

            self.prev_blocking_indi_node_candidate_hash =
                parent.use_blocking_indi_node_candidate_hash; // 413
            self.use_blocking_indi_node_candidate_hash =
                self.prev_blocking_indi_node_candidate_hash; // 414
            self.prev_blocking_indi_node_linked_candidate_hash =
                parent.use_blocking_indi_node_linked_candidate_hash; // 415
            self.use_blocking_indi_node_linked_candidate_hash =
                self.prev_blocking_indi_node_linked_candidate_hash; // 416
            self.prev_signature_blocking_review_set = parent.use_signature_blocking_review_set; // 417
            self.use_signature_blocking_review_set = self.prev_signature_blocking_review_set; // 418
            self.prev_early_indi_react_pro_queue = parent.use_early_indi_react_pro_queue; // 419
            self.use_early_indi_react_pro_queue = self.prev_early_indi_react_pro_queue; // 420
            self.prev_late_indi_react_pro_queue = parent.use_late_indi_react_pro_queue; // 421
            self.use_late_indi_react_pro_queue = self.prev_late_indi_react_pro_queue; // 422
            self.prev_reusing_review_set = parent.use_reusing_review_set; // 423
            self.use_reusing_review_set = self.prev_reusing_review_set; // 424
            self.prev_node_switch_history = parent.use_node_switch_history; // 425
            self.use_node_switch_history = self.prev_node_switch_history; // 426
            self.prev_indi_depth_first_process_queue = parent.use_indi_depth_first_process_queue; // 427
            self.use_indi_depth_first_process_queue = self.prev_indi_depth_first_process_queue; // 428
            self.prev_indi_imm_process_queue = parent.use_indi_imm_process_queue; // 429
            self.use_indi_imm_process_queue = self.prev_indi_imm_process_queue; // 430
            self.prev_delay_nom_process_queue = parent.use_delay_nom_process_queue; // 431
            self.use_delay_nom_process_queue = self.prev_delay_nom_process_queue; // 432
            self.prev_caching_loss_reactivation_process_queue =
                parent.use_caching_loss_reactivation_process_queue; // 433
            self.use_caching_loss_reactivation_process_queue =
                self.prev_caching_loss_reactivation_process_queue; // 434

            self.prev_delayed_backend_init_proc_queue = parent.use_delayed_backend_init_proc_queue; // 436
            self.use_delayed_backend_init_proc_queue = self.prev_delayed_backend_init_proc_queue; // 437

            self.prev_backend_neighbour_expansion = parent.use_backend_neighbour_expansion; // 439
            self.use_backend_neighbour_expansion = self.prev_backend_neighbour_expansion; // 440

            self.prev_role_assertion_process_queue = parent.use_role_assertion_process_queue; // 442
            self.use_role_assertion_process_queue = self.prev_role_assertion_process_queue; // 443
            self.prev_backend_sync_retest_process_queue =
                parent.use_backend_sync_retest_process_queue; // 444
            self.use_backend_sync_retest_process_queue =
                self.prev_backend_sync_retest_process_queue; // 445
            self.prev_backend_indirect_compatibility_expansion_queue =
                parent.use_backend_indirect_compatibility_expansion_queue; // 446
            self.use_backend_indirect_compatibility_expansion_queue =
                self.prev_backend_indirect_compatibility_expansion_queue; // 447
            self.prev_backend_direct_influence_expansion_queue =
                parent.use_backend_direct_influence_expansion_queue; // 448
            self.use_backend_direct_influence_expansion_queue =
                self.prev_backend_direct_influence_expansion_queue; // 449

            self.prev_backend_individual_reuse_expansion_queue =
                parent.use_backend_individual_reuse_expansion_queue; // 451
            self.use_backend_individual_reuse_expansion_queue =
                self.prev_backend_individual_reuse_expansion_queue; // 452
            self.backend_individual_late_reuse_expansion_activated =
                parent.backend_individual_late_reuse_expansion_activated; // 453
            self.prev_backend_late_individual_reuse_expansion_queue =
                parent.use_backend_late_individual_reuse_expansion_queue; // 454
            self.use_backend_late_individual_reuse_expansion_queue =
                self.prev_backend_late_individual_reuse_expansion_queue; // 455
            self.prev_backend_individual_neighbour_expansion_queue =
                parent.use_backend_individual_neighbour_expansion_queue; // 456
            self.use_backend_individual_neighbour_expansion_queue =
                self.prev_backend_individual_neighbour_expansion_queue; // 457

            self.prev_branching_tree = parent.use_branching_tree; // 459
            self.use_branching_tree = self.prev_branching_tree; // 460
            self.ontology_top_concept = parent.ontology_top_concept; // 461
            self.ontology_top_data_range_concept = parent.ontology_top_data_range_concept; // 462
            self.individual_node_cache_testing_linker =
                parent.individual_node_cache_testing_linker.clone(); // 463
            self.sorted_nominal_non_det_processing_node_linker =
                parent.sorted_nominal_non_det_processing_node_linker.clone(); // 464
            self.sorted_nominal_non_det_processing_nodes_sorted =
                parent.sorted_nominal_non_det_processing_nodes_sorted; // 465
            self.nominal_non_det_processing_count = parent.nominal_non_det_processing_count; // 466
            self.individual_node_resolve_linker = parent.individual_node_resolve_linker.clone(); // 467
            self.blockable_individual_node_updated_linker =
                parent.blockable_individual_node_updated_linker.clone(); // 468
            self.constructed_indi_node = parent.constructed_indi_node; // 469
            self.last_processing_indi_node = parent.last_processing_indi_node; // 470
            self.last_processing_con_des = parent.last_processing_con_des; // 471
            self.indi_process_node_linker = parent.indi_process_node_linker; // 472
            self.multiple_construction_indi_nodes = parent.multiple_construction_indi_nodes; // 473
            self.constructed_indi_node_initialized = parent.constructed_indi_node_initialized; // 474
            self.maximum_deterministic_branch_tag = parent.maximum_deterministic_branch_tag; // 475
            self.next_propagation_id = parent.next_propagation_id; // 476
            self.next_individual_node_id = parent.next_individual_node_id; // 477
            self.next_sat_res_succ_ext_individual_node_id =
                parent.next_sat_res_succ_ext_individual_node_id; // 478
            self.next_variable_id = parent.next_variable_id; // 479
            self.next_rep_variable_id = parent.next_rep_variable_id; // 480
            self.use_extended_concept_vector = parent.use_extended_concept_vector; // 481
            self.use_grounding_hash = parent.use_grounding_hash; // 482
            self.use_var_binding_path_merging_hash = parent.use_var_binding_path_merging_hash; // 483
            self.use_rep_var_bind_path_set_hash = parent.use_rep_var_bind_path_set_hash; // 484
            self.use_rep_var_bind_path_hash = parent.use_rep_var_bind_path_hash; // 485
            self.use_rep_var_bind_path_joining_key_hash =
                parent.use_rep_var_bind_path_joining_key_hash; // 486
            self.use_rep_joining_hash = parent.use_rep_joining_hash; // 487
            self.insufficient_node_occured = parent.insufficient_node_occured; // 488
            self.delayed_nominal_processing_occured = parent.delayed_nominal_processing_occured; // 489
            self.problematic_eq_candidate_node_occured =
                parent.problematic_eq_candidate_node_occured; // 490
            self.use_nom_caching_loss_react_hash = parent.use_nom_caching_loss_react_hash; // 491
            self.use_marker_indi_node_hash = parent.use_marker_indi_node_hash; // 492
            self.use_backend_concept_set_label_processing_hash =
                parent.use_backend_concept_set_label_processing_hash; // 493
            self.use_backend_loaded_association_hash = parent.use_backend_loaded_association_hash; // 494
            self.use_backend_neighbour_expansion_controlling_data =
                parent.use_backend_neighbour_expansion_controlling_data; // 495
            self.incremental_expansion_initialized = parent.incremental_expansion_initialized; // 496
            self.next_incremental_indi_exp_id = parent.next_incremental_indi_exp_id; // 497
            self.next_role_assertion_creation_id = parent.next_role_assertion_creation_id; // 498
            self.incremental_exp_id = parent.incremental_exp_id; // 499
            self.max_inc_prev_comp_graph_node_id = parent.max_inc_prev_comp_graph_node_id; // 500
            self.incremental_expansion_compatible_merged =
                parent.incremental_expansion_compatible_merged; // 501
            self.incremental_expansion_caching_merged = parent.incremental_expansion_caching_merged; // 502
            self.referred_indi_track_vec = parent.referred_indi_track_vec; // 503
            self.indi_dep_tracking_required = parent.indi_dep_tracking_required; // 504

            self.indi_saturation_process_node_linker =
                parent.indi_saturation_process_node_linker.clone(); // 507
            self.indi_saturation_completion_node_linker =
                parent.indi_saturation_completion_node_linker.clone(); // 508
            self.indi_saturation_completed_node_linker =
                parent.indi_saturation_completed_node_linker.clone(); // 509
            self.indi_saturation_analysing_node_linker =
                parent.indi_saturation_analysing_node_linker.clone(); // 510
            self.disjunct_common_concept_extract_processing_linker = parent
                .disjunct_common_concept_extract_processing_linker
                .clone(); // 511
            self.nominal_delayed_indi_saturation_process_node_linker = parent
                .nominal_delayed_indi_saturation_process_node_linker
                .clone(); // 512
            self.saturation_atmost_merging_process_linker =
                parent.saturation_atmost_merging_process_linker.clone(); // 513
            self.use_indi_vector = parent.use_indi_vector; // 514

            self.backend_cache_update_individuals_initialized =
                parent.backend_cache_update_individuals_initialized; // 516
            self.representative_neighbour_expansion_individual_node_linker = parent
                .representative_neighbour_expansion_individual_node_linker
                .clone(); // 517

            // `.cpp` 519–536: lazy-init the saturation satellites from the parent's.
            if let Some(parent_vec) = parent.indi_saturation_process_vector.as_ref() {
                self.individual_saturation_process_node_vector(true)
                    .expect("create=true yields CIndividualSaturationProcessNodeVector")
                    .reference_vector(parent_vec);
            }
            if let Some(ctx) = process_context.as_deref_mut() {
                self.copy_parent_saturation_satellites(parent, ctx);
            }
        }
        // `.cpp` 539: mIndiProcessVector->referenceVector(prevIndiProcVec).
        // The vector is owned by value in Rust, so reference-vector handoff is a
        // content clone from the saved parent vector.
        self.indi_process_vector = prev_indi_proc_vec;
        self
    }

    fn copy_parent_saturation_satellites(
        &mut self,
        parent: &ProcessingDataBox,
        process_context: &mut ProcessContext,
    ) {
        if parent.sat_influenced_nominal_set.is_some() {
            let parent_set = process_context
                .sat_influenced_nominal_set(parent.sat_influenced_nominal_set)
                .clone();
            let child_set =
                process_context.processing_data_box_saturation_influenced_nominal_set(self, true);
            process_context
                .sat_influenced_nominal_set_mut(child_set)
                .init_influenced_nominal_set(Some(&parent_set));
        }
        if parent.sat_nominal_dependent_node_hash.is_some() {
            let parent_hash = process_context
                .sat_nominal_dependent_node_hash(parent.sat_nominal_dependent_node_hash)
                .clone();
            let child_hash = process_context
                .processing_data_box_saturation_nominal_dependent_node_hash(self, true);
            process_context
                .sat_nominal_dependent_node_hash_mut(child_hash)
                .init_nominal_dependent_node_hash(Some(&parent_hash));
        }
        if parent.sat_critical_indi_node_con_test_set.is_some() {
            let parent_set = process_context
                .sat_critical_ind_node_con_test_set(parent.sat_critical_indi_node_con_test_set)
                .clone();
            let child_set = process_context
                .processing_data_box_saturation_critical_individual_node_concept_test_set(
                    self, true,
                );
            process_context
                .sat_critical_ind_node_con_test_set_mut(child_set)
                .init_individual_node_concept_test_set(Some(&parent_set));
        }
        if parent.sat_succ_ext_ind_node_proc_queue.is_some() {
            let parent_queue = process_context
                .sat_succ_ext_ind_node_proc_queue(parent.sat_succ_ext_ind_node_proc_queue)
                .clone();
            let child_queue = process_context
                .processing_data_box_saturation_successor_extension_individual_node_processing_queue(
                    self, true,
                );
            process_context
                .sat_succ_ext_ind_node_proc_queue_mut(child_queue)
                .init_processing_queue(Some(&parent_queue));
        }
        if parent.sat_critical_indi_node_proc_queue.is_some() {
            let parent_queue = process_context
                .sat_critical_ind_node_proc_queue(parent.sat_critical_indi_node_proc_queue)
                .clone();
            let child_queue = process_context
                .processing_data_box_saturation_critical_individual_node_processing_queue(
                    self, true,
                );
            process_context
                .sat_critical_ind_node_proc_queue_mut(child_queue)
                .init_processing_queue(Some(&parent_queue));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::{NodeId, SatNodeId};
    use super::*;

    #[test]
    fn db1_parent_init_references_parent_individual_process_vector() {
        let mut parent = ProcessingDataBox::new();
        let pos_node = NodeId::new(11);
        let neg_node = NodeId::new(12);
        parent
            .individual_process_node_vector_mut()
            .set_local_data(5, pos_node)
            .set_local_data(-3, neg_node);

        let mut child = ProcessingDataBox::new();
        child.init_processing_data_box_parent(Some(&parent));

        assert_eq!(child.individual_process_node_vector().get_data(5), pos_node);
        assert_eq!(
            child.individual_process_node_vector().get_data(-3),
            neg_node
        );

        child
            .individual_process_node_vector_mut()
            .set_local_data(5, NodeId::new(99));
        assert_eq!(
            parent.individual_process_node_vector().get_data(5),
            pos_node
        );
        assert_eq!(
            child.individual_process_node_vector().get_data(5),
            NodeId::new(99)
        );
    }

    #[test]
    fn db1_parent_init_references_parent_individual_saturation_vector() {
        let mut parent = ProcessingDataBox::new();
        let parent_node = SatNodeId::new(17);
        parent
            .individual_saturation_process_node_vector(true)
            .expect("create=true yields CIndividualSaturationProcessNodeVector")
            .set_data(9, parent_node);

        let mut child = ProcessingDataBox::new();
        child.init_processing_data_box_parent(Some(&parent));

        assert_eq!(
            child
                .individual_saturation_process_node_vector_ref()
                .expect("parent vector is referenced")
                .get_data(9),
            parent_node
        );
        assert_eq!(
            child
                .individual_saturation_process_node_vector_ref()
                .expect("parent vector is referenced")
                .get_item_count(),
            10
        );

        child
            .individual_saturation_process_node_vector(true)
            .expect("create=true yields CIndividualSaturationProcessNodeVector")
            .set_data(9, SatNodeId::new(99));
        assert_eq!(
            parent
                .individual_saturation_process_node_vector_ref()
                .expect("parent keeps its own vector")
                .get_data(9),
            parent_node
        );
    }

    #[test]
    fn db1_parent_init_with_context_copies_real_saturation_satellites() {
        let mut context = ProcessContext::new();
        let mut parent = ProcessingDataBox::new();

        let influenced =
            context.processing_data_box_saturation_influenced_nominal_set(&mut parent, true);
        context
            .sat_influenced_nominal_set_mut(influenced)
            .set_nominal_influenced(41);

        let nominal_hash =
            context.processing_data_box_saturation_nominal_dependent_node_hash(&mut parent, true);
        let nominal_data = context.sat_nominal_dependent_node_hash_add_nominal_dependent_node(
            nominal_hash,
            17,
            SatNodeId::new(21),
            super::super::stubs::SaturationNominalConnectionType::NominalConnection,
        );

        let concept_set = context
            .processing_data_box_saturation_critical_individual_node_concept_test_set(
                &mut parent,
                true,
            );
        context
            .sat_critical_ind_node_con_test_set_mut(concept_set)
            .insert_concept_tested_for_individual(ConceptId::new(7), SatNodeId::new(8));

        let succ_queue = context
            .processing_data_box_saturation_successor_extension_individual_node_processing_queue(
                &mut parent,
                true,
            );
        context
            .sat_succ_ext_ind_node_proc_queue_mut(succ_queue)
            .insert_process_individual(SatNodeId::new(31), 31)
            .insert_process_individual(SatNodeId::new(32), 32)
            .take_next_to_current_process_individual();

        let critical_queue = context
            .processing_data_box_saturation_critical_individual_node_processing_queue(
                &mut parent,
                true,
            );
        context
            .sat_critical_ind_node_proc_queue_mut(critical_queue)
            .insert_process_individual(SatNodeId::new(43), 43);

        let mut child = ProcessingDataBox::new();
        child.init_processing_data_box_parent_with_process_context(Some(&parent), &mut context);

        assert!(child.sat_influenced_nominal_set.is_some());
        assert_ne!(
            child.sat_influenced_nominal_set,
            parent.sat_influenced_nominal_set
        );
        assert!(context
            .sat_influenced_nominal_set(child.sat_influenced_nominal_set)
            .is_nominal_influenced(41));

        assert!(child.sat_nominal_dependent_node_hash.is_some());
        assert_ne!(
            child.sat_nominal_dependent_node_hash,
            parent.sat_nominal_dependent_node_hash
        );
        assert_eq!(
            context
                .sat_nominal_dependent_node_hash(child.sat_nominal_dependent_node_hash)
                .get_nominal_dependent_node_data(17),
            nominal_data
        );

        assert!(child.sat_critical_indi_node_con_test_set.is_some());
        assert_ne!(
            child.sat_critical_indi_node_con_test_set,
            parent.sat_critical_indi_node_con_test_set
        );
        assert!(context
            .sat_critical_ind_node_con_test_set(child.sat_critical_indi_node_con_test_set)
            .is_concept_tested_for_individual(ConceptId::new(7), SatNodeId::new(8)));

        assert!(child.sat_succ_ext_ind_node_proc_queue.is_some());
        assert_ne!(
            child.sat_succ_ext_ind_node_proc_queue,
            parent.sat_succ_ext_ind_node_proc_queue
        );
        assert_eq!(
            context
                .sat_succ_ext_ind_node_proc_queue(child.sat_succ_ext_ind_node_proc_queue)
                .get_current_process_individual(),
            SatNodeId::new(32)
        );
        assert!(context
            .sat_succ_ext_ind_node_proc_queue(child.sat_succ_ext_ind_node_proc_queue)
            .is_individual_queued(SatNodeId::new(31), 31));

        assert!(child.sat_critical_indi_node_proc_queue.is_some());
        assert_ne!(
            child.sat_critical_indi_node_proc_queue,
            parent.sat_critical_indi_node_proc_queue
        );
        assert!(context
            .sat_critical_ind_node_proc_queue(child.sat_critical_indi_node_proc_queue)
            .is_individual_queued(43));
    }

    #[test]
    fn db1_parent_init_with_context_leaves_absent_parent_satellites_absent() {
        let mut context = ProcessContext::new();
        let parent = ProcessingDataBox::new();
        let mut child = ProcessingDataBox::new();

        context.processing_data_box_saturation_influenced_nominal_set(&mut child, true);
        context.processing_data_box_saturation_nominal_dependent_node_hash(&mut child, true);
        context.processing_data_box_saturation_critical_individual_node_concept_test_set(
            &mut child, true,
        );
        context
            .processing_data_box_saturation_successor_extension_individual_node_processing_queue(
                &mut child, true,
            );
        context.processing_data_box_saturation_critical_individual_node_processing_queue(
            &mut child, true,
        );

        child.init_processing_data_box_parent_with_process_context(Some(&parent), &mut context);

        assert!(child.sat_influenced_nominal_set.is_none());
        assert!(child.sat_nominal_dependent_node_hash.is_none());
        assert!(child.sat_critical_indi_node_con_test_set.is_none());
        assert!(child.sat_succ_ext_ind_node_proc_queue.is_none());
        assert!(child.sat_critical_indi_node_proc_queue.is_none());
    }

    #[test]
    fn db1_constructor_initializes_individual_process_vector() {
        let data_box = ProcessingDataBox::with_process_context(42);

        assert_eq!(data_box.process_context, 42);
        assert_eq!(
            data_box.individual_process_node_vector().get_data(0),
            NodeId::NONE
        );
    }

    #[test]
    fn db1_resolved_ontology_init_assigns_available_getter_results() {
        let mut data_box = ProcessingDataBox::new();
        let top_concept = ConceptId::new(17);
        let top_data_range_concept = ConceptId::new(23);

        data_box.init_processing_data_box_ontology_resolved(
            101,
            top_concept,
            top_data_range_concept,
            Id::NONE,
            Id::NONE,
        );

        assert_eq!(data_box.ontology, 101);
        assert_eq!(data_box.ontology_top_concept, top_concept);
        assert_eq!(
            data_box.ontology_top_data_range_concept,
            top_data_range_concept
        );
        assert!(data_box.use_extended_concept_vector.is_none());
        assert!(data_box.use_indi_vector.is_none());
    }

    #[test]
    fn db1_parent_init_without_parent_resets_individual_process_vector() {
        let mut data_box = ProcessingDataBox::new();
        data_box
            .individual_process_node_vector_mut()
            .set_local_data(4, NodeId::new(21))
            .set_local_data(-2, NodeId::new(22));

        data_box.init_processing_data_box_parent(None);

        assert_eq!(
            data_box.individual_process_node_vector().get_data(4),
            NodeId::NONE
        );
        assert_eq!(
            data_box.individual_process_node_vector().get_data(-2),
            NodeId::NONE
        );
    }
}
