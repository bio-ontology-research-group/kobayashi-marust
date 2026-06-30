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
use super::databox::ProcessingDataBox;
use super::node_resolution::IndividualProcessNodeVector;

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
        // W2-DEFER[api]: mIndiProcessVector =
        //   CObjectParameterizingAllocator<CIndividualProcessNodeVector,...>::
        //   allocateAndConstructAndParameterize(... , mProcessContext);
        // (the per-test arena allocation of the node vector is owned by the
        // not-yet-ported CProcessContext) — left as `Id::NONE`.
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
        // `.cpp` 269: mOntology = ontology;
        self.ontology = ontology;
        // W2-DEFER[api]: mOntologyTopConcept = mOntology->getTBox()->getTopConcept();
        // (CConcreteOntology / CTBox not yet ported) — left as `Id::NONE`.
        self.ontology_top_concept = Id::NONE;
        // W2-DEFER[api]: mOntologyTopDataRangeConcept =
        //   mOntology->getTBox()->getTopDataRangeConcept();
        self.ontology_top_data_range_concept = Id::NONE;
        // W2-DEFER[api]: mUseExtendedConceptVector =
        //   mOntology->getTBox()->getConceptVector(false);
        self.use_extended_concept_vector = Id::NONE;
        // W2-DEFER[api]: mUseIndiVector =
        //   mOntology->getABox()->getIndividualVector(false);
        self.use_indi_vector = Id::NONE;
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
    pub fn init_processing_data_box_parent(&mut self, parent: Option<&ProcessingDataBox>) -> &mut Self {
        // `.cpp` 285: CIndividualProcessNodeVector* prevIndiProcVec = nullptr;
        // KONCLUDE-PORT-NOTE[ownership]: the node vector is now a real ported type held
        // BY VALUE on the databox (node-resolution keystone); this save-local captures a
        // clone of the parent's, preserving the existing (deferred) save/restore body.
        let mut prev_indi_proc_vec: IndividualProcessNodeVector = IndividualProcessNodeVector::new();

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
        self.indi_process_node_linker.clear(); // 296
        self.rem_sat_update_linker.clear(); // 297
        self.rem_sat_indi_node_linker.clear(); // 298
        self.rem_sat_indi_succ_link_data_linker.clear(); // 299
        self.rem_con_sat_des.clear(); // 300
        self.rem_con_des.clear(); // 301
        self.rem_role_sat_process_linker.clear(); // 302

        self.indi_saturation_process_node_linker.clear(); // 304
        self.indi_saturation_completion_node_linker.clear(); // 305
        self.indi_saturation_completed_node_linker.clear(); // 306
        self.indi_saturation_analysing_node_linker.clear(); // 307
        self.saturation_atmost_merging_process_linker.clear(); // 308
        self.nominal_delayed_indi_saturation_process_node_linker.clear(); // 309
        self.disjunct_common_concept_extract_processing_linker.clear(); // 310
        self.rem_con_sat_process_linker.clear(); // 311
        self.indi_saturation_process_vector = Id::NONE; // 312
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
        self.current_merged_possible_instance_individual_linkers_linker.clear(); // 363
        self.last_backend_cache_integrated_indi_node_linker.clear(); // 364
        self.backend_cache_integrated_individual_node_count = 0; // 365
        self.backend_cache_integrated_same_individual_node_count = 0; // 366
        self.local_indi_vector = Id::NONE; // 367
        self.backend_cache_update_individuals_initialized = false; // 368
        self.representative_neighbour_expansion_individual_node_linker.clear(); // 369

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
            self.last_merged_possible_instance_individual_linker =
                parent.last_merged_possible_instance_individual_linker.clone(); // 376
            self.current_merged_possible_instance_individual_linkers_linker =
                parent.current_merged_possible_instance_individual_linkers_linker.clone(); // 377
            self.last_backend_cache_integrated_indi_node_linker =
                parent.last_backend_cache_integrated_indi_node_linker.clone(); // 378
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
            self.prev_signature_blocking_review_set =
                parent.use_signature_blocking_review_set; // 417
            self.use_signature_blocking_review_set =
                self.prev_signature_blocking_review_set; // 418
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
            self.indi_process_node_linker = parent.indi_process_node_linker.clone(); // 472
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
            self.disjunct_common_concept_extract_processing_linker =
                parent.disjunct_common_concept_extract_processing_linker.clone(); // 511
            self.nominal_delayed_indi_saturation_process_node_linker =
                parent.nominal_delayed_indi_saturation_process_node_linker.clone(); // 512
            self.saturation_atmost_merging_process_linker =
                parent.saturation_atmost_merging_process_linker.clone(); // 513
            self.use_indi_vector = parent.use_indi_vector; // 514

            self.backend_cache_update_individuals_initialized =
                parent.backend_cache_update_individuals_initialized; // 516
            self.representative_neighbour_expansion_individual_node_linker =
                parent.representative_neighbour_expansion_individual_node_linker.clone(); // 517

            // `.cpp` 519–536: lazy-init the saturation satellites from the parent's.
            // W2-DEFER[api]: the `getX(true)` localised getters (DB-2/DB-5) and the
            // `referenceVector`/`init*` methods on the not-yet-ported saturation
            // container classes. Guards preserved; bodies are no-ops for now.
            if parent.indi_saturation_process_vector.is_some() {
                // W2-DEFER[api]: getIndividualSaturationProcessNodeVector(true)
                //   ->referenceVector(parent.mIndiSaturationProcessVector);
            }
            if parent.sat_influenced_nominal_set.is_some() {
                // W2-DEFER[api]: getSaturationInfluencedNominalSet(true)
                //   ->initInfluencedNominalSet(parent.mSatInfluencedNominalSet);
            }
            if parent.sat_nominal_dependent_node_hash.is_some() {
                // W2-DEFER[api]: getSaturationNominalDependentNodeHash(true)
                //   ->initNominalDependentNodeHash(parent.mSatNominalDependentNodeHash);
            }
            if parent.sat_critical_indi_node_con_test_set.is_some() {
                // W2-DEFER[api]: getSaturationCriticalIndividualNodeConceptTestSet(true)
                //   ->initIndividualNodeConceptTestSet(parent.mSatCriticalIndiNodeConTestSet);
            }
            if parent.sat_succ_ext_ind_node_proc_queue.is_some() {
                // W2-DEFER[api]: getSaturationSucessorExtensionIndividualNodeProcessingQueue(true)
                //   ->initProcessingQueue(parent.mSatSuccExtIndNodeProcQueue);
            }
            if parent.sat_critical_indi_node_proc_queue.is_some() {
                // W2-DEFER[api]: getSaturationCriticalIndividualNodeProcessingQueue(true)
                //   ->initProcessingQueue(parent.mSatCriticalIndiNodeProcQueue);
            }
        }
        // `.cpp` 539: mIndiProcessVector->referenceVector(prevIndiProcVec);
        // W2-DEFER[api]: `referenceVector` on the not-yet-ported
        // CIndividualProcessNodeVector; the prev-vector handle is captured above.
        let _ = prev_indi_proc_vec;
        self
    }
}
