//! `cache::backend_facade3` — F1 facade method bodies, **LAST THIRD**.
//!
//! Port of the final third of `CBackendRepresentativeMemoryCache::*` method
//! definitions from
//! `Source/Reasoner/Kernel/Cache/CBackendRepresentativeMemoryCache.cpp`
//! (function-by-function; see `PORT.md` §44). C++ source line range taken:
//! **3958..5343** (def of `checkBasicPrecompuationModeActivation` through the
//! final `copyNeighbourIndividualIdLinkers`). The facade struct + fields live in
//! `cache/backend.rs`; this file only adds an `impl` block of these 20 methods.
//! The preceding thirds (precompute/precondition + the big install/event spine,
//! incl. `processCustomsEvents`) belong to `backend_facade1` / `backend_facade2`.
//!
//! ## What is real vs deferred here
//!
//! The "retrieval/reading + debug-stringify + facade utility" tail divides into:
//! * **Real ports** (self-contained, no facade-arena deref): the label-type →
//!   string switch; the three `KONCLUDE_CACHE_DEBUGGING_DATA_GENERATION`-gated
//!   debug checks (whose entire body is behind the build macro → trivial in a
//!   normal build); the file-writer + the ontology-loop stringify driver (over
//!   the real `ontology_identifier_data_hash` field).
//! * **`W6-DEFER[api]`**: every method whose body dereferences the DEEP F1
//!   storage — `OntologyData` / `IndividualAssociationData` / `LabelCacheItem` /
//!   `IndividualRoleSetNeighbourArray` (held in facade-arenas not yet wired onto
//!   the facade struct in this wave, exactly as the W3 `W3-DEFER[api]` precedent).
//!   The C++ logic is summarised in each comment so the reconcile pass can fill
//!   it once `backend_data` method bodies + the cache `ProcessContext`-analogue
//!   arenas land. No logic is silently dropped.
//!
//! ## License (per `PORT.md` §License note)
//! Function-by-function translation of LGPLv3 Konclude source; LGPL terms attach.

#![allow(dead_code)]
#![allow(unused_variables)]

use std::io::Write;

use super::super::model::substrate::{Cint64, INVALID};
use super::backend::BackendRepresentativeMemoryCache;
use super::backend_data::{
    BackendTempWriteRecordId, IndividualAssociationData, IndividualAssociationDataId,
    IndividualRoleSetNeighbourArray, IndividualRoleSetNeighbourArrayId,
    IndividualRoleSetNeighbourData, IndividualRoleSetNeighbourIndividualIdLinker,
    IndividualRoleSetNeighbourIndividualIdLinkerId, LabelCacheItem, LabelCacheItemExtensionData,
    LabelCacheItemExtensionType, LabelCacheItemId, LabelCacheItemType, LabelValueLinker,
    OntologyData, OntologyDataId, LABEL_CACHE_ITEM_ASSOCIATABLE_TYPE_COUNT,
};
use super::context::CacheContext;
use super::value::{CacheValue, CacheValueIdentifier};

impl BackendRepresentativeMemoryCache {
    // =======================================================================
    // Basic-precomputation-mode activation
    // =======================================================================

    /// Port of `CBackendRepresentativeMemoryCache::checkBasicPrecompuationModeActivation`.
    ///
    /// Returns true when the current direct-update/merge ratio should activate
    /// basic-precomputation mode.
    pub fn check_basic_precompuation_mode_activation(
        &self,
        ontology_data: OntologyDataId,
        cache_context: &CacheContext,
    ) -> bool {
        if ontology_data.is_none() {
            return false;
        }
        let ontology_data = cache_context.ontology_data(ontology_data);
        if !ontology_data.is_association_completed()
            && !ontology_data.has_basic_precomputation_mode_activation()
            && ontology_data.get_incompletely_handled_individual_id_count() > 0
            && self.conf_basic_precomputation_mode_activation_update_merges_ratio > 0.0
        {
            let basic_indi_update_count =
                ontology_data.get_individual_association_data_direct_update_count() as f64;
            let indi_merges_count = ontology_data.get_individual_association_merging_count() as f64;

            if indi_merges_count > 0.0 {
                let ratio = indi_merges_count / basic_indi_update_count;
                if ratio > self.conf_basic_precomputation_mode_activation_update_merges_ratio {
                    return true;
                }
            }
        }
        false
    }

    /// Port of `CBackendRepresentativeMemoryCache::activateBasicPrecompuationMode`.
    pub fn activate_basic_precompuation_mode(
        &mut self,
        ontology_data: OntologyDataId,
        cache_context: &mut CacheContext,
    ) -> bool {
        if ontology_data.is_none() {
            return false;
        }

        let should_activate = {
            let data = cache_context.ontology_data(ontology_data);
            !data.is_basic_precomputation_mode() && !data.has_basic_precomputation_mode_activation()
        };
        if should_activate {
            let data = cache_context.ontology_data_mut(ontology_data);
            data.set_basic_precomputation_mode_activation(true);
            data.set_basic_precomputation_mode(true);

            let _context = data.get_ontology_context();
            let _basic_indi_update_count =
                data.get_individual_association_data_direct_update_count();
            let _indi_merges_count = data.get_individual_association_merging_count();

            let indi_id_asso_data_vector = data.get_individual_id_assoiation_data_vector().to_vec();
            let indi_id_asso_data_vector_size =
                data.get_individual_id_assoiation_data_vector_size();
            data.set_basic_precomputation_individual_id_assoiation_data_vector(
                indi_id_asso_data_vector_size,
                indi_id_asso_data_vector,
            );
            return true;
        }
        false
    }

    /// Port of `CBackendRepresentativeMemoryCache::indexIndividualLabelAssociations`.
    ///
    pub fn index_individual_label_associations(
        &mut self,
        ontology_data: OntologyDataId,
        cache_context: &mut CacheContext,
    ) {
        if ontology_data.is_none() {
            return;
        }
        let mut indexing_count = 0;
        for i in 0..LABEL_CACHE_ITEM_ASSOCIATABLE_TYPE_COUNT {
            if self.requires_individual_associations(i as Cint64) {
                indexing_count += 1;
            }
        }
        let (indi_count, vec_size, indi_id_asso_data_vector) = {
            let data = cache_context.ontology_data_mut(ontology_data);
            data.set_individual_label_association_indexing_count(indexing_count);
            (
                data.get_max_stored_indvidual_id(),
                data.get_individual_id_assoiation_data_vector_size(),
                data.get_individual_id_assoiation_data_vector().to_vec(),
            )
        };

        for i in 0..LABEL_CACHE_ITEM_ASSOCIATABLE_TYPE_COUNT {
            let exact_indi_assoc_tracking = self.requires_individual_associations(i as Cint64);
            if exact_indi_assoc_tracking {
                let mut indi_id = 0;
                while indi_id <= indi_count && indi_id < vec_size {
                    let indi_ass_data = indi_id_asso_data_vector
                        .get(indi_id as usize)
                        .copied()
                        .unwrap_or(IndividualAssociationDataId::NONE);
                    if indi_ass_data.is_some() {
                        let label_item = cache_context
                            .individual_assoc_data(indi_ass_data)
                            .get_label_cache_entry(i as Cint64);
                        if label_item.is_some() {
                            let indi_asso_ext_data = self
                                .get_individual_associations_extension_data(
                                    label_item,
                                    ontology_data,
                                    cache_context,
                                );
                            if indi_asso_ext_data.is_some() {
                                let (associated_id, same_merged) = {
                                    let ass_data =
                                        cache_context.individual_assoc_data(indi_ass_data);
                                    (
                                        ass_data.get_associated_individual_id(),
                                        ass_data.has_representative_same_individual_merging(),
                                    )
                                };
                                cache_context
                                    .label_cache_item_ext_data_mut(indi_asso_ext_data)
                                    .add_individual_id_association(associated_id, same_merged);
                            }
                        }
                    }
                    indi_id += 1;
                }
                let remaining_count = cache_context
                    .ontology_data_mut(ontology_data)
                    .update_individual_label_association_indexed(true, INVALID);
                let _ = remaining_count;
            }
        }

        if self.conf_wait_individual_label_association_indexed {
            cache_context
                .ontology_data_mut(ontology_data)
                .wait_individual_label_association_indexed();
        }
    }

    // =======================================================================
    // Propagation-cut integration
    // =======================================================================

    /// Port of `CBackendRepresentativeMemoryCache::integratePropagationCut`.
    ///
    /// W6-DEFER[api]: the largest reading/update method in this third. It walks the
    /// `TemporaryPropagationCutDataLinker` chain, resolves each cut individual's
    /// `IndividualRoleSetNeighbourArray`, and — for every non-expanded neighbour —
    /// decides (by non-deterministic role-set elements / propagated-concept presence
    /// / cardinality extension) whether the neighbour must be re-marked
    /// incompletely-handled, either directly (`update_propagation_cut_individual_incompletely_handled`
    /// for deterministically propagated concepts when
    /// `conf_propagation_cut_propagated_concept_direct_installation`) or via the
    /// prioritized propagation-marked neighbour label item
    /// (`update_propagation_cut_individual_incompletely_handled_list`). It also fills
    /// the `tmp_prop_cut_indi_array_neighbours_handling_data_hash`
    /// readding/reduction/removal array-position sets and lazily creates the
    /// prioritized propagation-marked `NEIGHBOUR_INSTANTIATED_ROLE_SET_LABEL` item.
    /// All of these touch facade-arena deep storage not yet wired. Restore on the
    /// reconcile pass; returns whether any neighbour was updated.
    pub fn integrate_propagation_cut(
        &mut self,
        tmp_prop_cut_data_linker: BackendTempWriteRecordId,
        ontology_data: OntologyDataId,
    ) -> bool {
        // W6-DEFER[api]: facade-arena deref over the whole neighbour-array walk (see doc-comment).
        let _ = (tmp_prop_cut_data_linker, ontology_data);
        false
    }

    /// Port of `CBackendRepresentativeMemoryCache::updatePropagationCutIndividualIncompletelyHandled`
    /// (the `const CCacheValue&` overload).
    ///
    /// W6-DEFER[api]: localises the neighbour's `IndividualAssociationData`, extends
    /// its `FULL_CONCEPT_SET_LABEL` by `propConValue` (`get_extended_label`), bumps
    /// the update id, and re-marks it incompletely handled (directly or via the
    /// representative-referenced path), then publishes via
    /// `set_updated_individual_association_data`. Derefs deep storage; restore on
    /// reconcile. Always returns true in the C++.
    pub fn update_propagation_cut_individual_incompletely_handled(
        &mut self,
        neighbour_id: Cint64,
        prop_con_value: &CacheValue,
        ontology_data: OntologyDataId,
    ) -> bool {
        // W6-DEFER[api]: facade-arena deref (createLocalized… / getExtendedLabel / …).
        let _ = (neighbour_id, prop_con_value, ontology_data);
        true
    }

    /// Port of `CBackendRepresentativeMemoryCache::updatePropagationCutIndividualIncompletelyHandled`
    /// (the `const QList<cint64>&` + `propMarkLabelItem` overload).
    ///
    /// KONCLUDE-PORT-NOTE[overload]: Rust cannot overload; the `QList<cint64>` variant
    /// takes the `_list` suffix. Callers (`integrate_propagation_cut`) must target this name.
    ///
    /// W6-DEFER[api]: when the neighbour has no representative same-individual merging,
    /// localises it, extends the `NEIGHBOUR_INSTANTIATED_ROLE_SET_COMBINATION_LABEL`
    /// by the prop-mark label item, rebuilds the neighbour role-set array (reindexing
    /// to the new combination label), appends the not-yet-present propagation-cut
    /// individual ids under the prop-mark array index, copies the role-set hash, bumps
    /// the update id, re-marks incompletely handled, and publishes. Returns true when
    /// it acted, false when the neighbour was representative-merged. Derefs deep storage.
    pub fn update_propagation_cut_individual_incompletely_handled_list(
        &mut self,
        neighbour_id: Cint64,
        prop_cut_indi_id_list: &[Cint64],
        prop_mark_label_item: LabelCacheItemId,
        ontology_data: OntologyDataId,
    ) -> bool {
        // W6-DEFER[api]: facade-arena deref over the role-set-array rebuild (see doc-comment).
        let _ = (
            neighbour_id,
            prop_cut_indi_id_list,
            prop_mark_label_item,
            ontology_data,
        );
        false
    }

    /// Port of `CBackendRepresentativeMemoryCache::updateInvolvedIndividuals`.
    ///
    /// W6-DEFER[api]: walks the `TemporaryInvolvedIndividualDataLinker` involved-id
    /// chain, raising each individual's problematic level (and the ontology's involved
    /// count for newly-involved ones), gathers the neighbour ids whose arrays must be
    /// reordered, and for each rebuilds the role-set neighbour array so that
    /// problematic/involved neighbours sort to the front, re-marking the rebuilt
    /// association incompletely handled and publishing it. Returns whether anything
    /// was updated. Derefs deep storage + [memory-pool] linker allocation.
    pub fn update_involved_individuals(
        &mut self,
        tmp_involved_indi_data_linker: BackendTempWriteRecordId,
        ontology_data: OntologyDataId,
    ) -> bool {
        // W6-DEFER[api]: facade-arena deref over the neighbour-array reorder (see doc-comment).
        let _ = (tmp_involved_indi_data_linker, ontology_data);
        false
    }

    // =======================================================================
    // Stringification / file dump (debug utilities)
    // =======================================================================

    /// Port of `CBackendRepresentativeMemoryCache::writeStringifiedRepresentativeCacheToFile`.
    ///
    /// Faithful I/O port: dumps `get_representative_cache_string()` to both the
    /// "latest" file and a write-count-numbered file under `./Debugging/RepresentativeCache/`.
    /// KONCLUDE-PORT-NOTE[macro]: the trailing `KONCLUDE_CACHE_DEBUGGING_DATA_GENERATION`
    /// block dumping `mDebugHandlingStrings` is build-flag-gated and the debug member
    /// is omitted from the facade struct (see `backend.rs` struct doc) → omitted here.
    pub fn write_stringified_representative_cache_to_file(&self) {
        let model_string_list = self.get_representative_cache_string();
        if let Ok(mut model_file_latest) = std::fs::File::create(
            "./Debugging/RepresentativeCache/individual-label-association-data.txt",
        ) {
            for model_string in &model_string_list {
                let _ = model_file_latest.write_all(model_string.as_bytes());
            }
        }
        let numbered_path = format!(
            "./Debugging/RepresentativeCache/individual-label-association-data-{}.txt",
            self.write_data_count
        );
        if let Ok(mut model_file) = std::fs::File::create(&numbered_path) {
            for model_string in &model_string_list {
                let _ = model_file.write_all(model_string.as_bytes());
            }
        }
        // KONCLUDE-PORT-NOTE[macro]: KONCLUDE_CACHE_DEBUGGING_DATA_GENERATION
        // handling-data.txt dump (mDebugHandlingStrings) omitted (build-flag only).
    }

    /// Port of `CBackendRepresentativeMemoryCache::getRepresentativeCacheLabelItemString`.
    ///
    /// Fully self-contained: maps a label-type code to its symbolic name (empty string
    /// for unmatched, matching the C++).
    pub fn get_representative_cache_label_item_string(&self, label_type: Cint64) -> String {
        let mut label_type_string = String::new();
        if label_type == LabelCacheItemType::DeterministicConceptSetLabel as Cint64 {
            label_type_string = "DETERMINISTIC_CONCEPT_SET_LABEL".to_string();
        } else if label_type == LabelCacheItemType::NondeterministicConceptSetLabel as Cint64 {
            label_type_string = "NONDETERMINISTIC_CONCEPT_SET_LABEL".to_string();
        } else if label_type == LabelCacheItemType::FullConceptSetLabel as Cint64 {
            label_type_string = "FULL_CONCEPT_SET_LABEL".to_string();
        } else if label_type
            == LabelCacheItemType::DeterministicCombinedExistentialInstantiatedRoleSetLabel
                as Cint64
        {
            label_type_string =
                "DETERMINISTIC_COMBINED_EXISTENTIAL_INSTANTIATED_ROLE_SET_LABEL".to_string();
        } else if label_type
            == LabelCacheItemType::NondeterministicCombinedExistentialInstantiatedRoleSetLabel
                as Cint64
        {
            label_type_string =
                "NONDETERMINISTIC_COMBINED_EXISTENTIAL_INSTANTIATED_ROLE_SET_LABEL".to_string();
        } else if label_type
            == LabelCacheItemType::DeterministicCombinedNeighbourInstantiatedRoleSetLabel as Cint64
        {
            label_type_string =
                "DETERMINISTIC_COMBINED_NEIGHBOUR_INSTANTIATED_ROLE_SET_LABEL".to_string();
        } else if label_type
            == LabelCacheItemType::NondeterministicCombinedNeighbourInstantiatedRoleSetLabel
                as Cint64
        {
            label_type_string =
                "NONDETERMINISTIC_COMBINED_NEIGHBOUR_INSTANTIATED_ROLE_SET_LABEL".to_string();
        } else if label_type
            == LabelCacheItemType::NeighbourInstantiatedRoleSetCombinationLabel as Cint64
        {
            label_type_string = "NEIGHBOUR_INSTANTIATED_ROLE_SET_COMBINATION_LABEL".to_string();
        } else if label_type == LabelCacheItemType::DeterministicSameIndividualSetLabel as Cint64 {
            label_type_string = "DETERMINISTIC_SAME_INDIVIDUAL_SET_LABEL".to_string();
        } else if label_type == LabelCacheItemType::NondeterministicSameIndividualSetLabel as Cint64
        {
            label_type_string = "NONDETERMINISTIC_SAME_INDIVIDUAL_SET_LABEL".to_string();
        } else if label_type
            == LabelCacheItemType::DeterministicDiffrentIndividualSetLabel as Cint64
        {
            label_type_string = "DETERMINISTIC_DIFFRENT_INDIVIDUAL_SET_LABEL".to_string();
        } else if label_type
            == LabelCacheItemType::NondeterministicDiffrentIndividualSetLabel as Cint64
        {
            label_type_string = "NONDETERMINISTIC_DIFFRENT_INDIVIDUAL_SET_LABEL".to_string();
        } else if label_type
            == LabelCacheItemType::IndirectlyConnectedNominalIndividualSetLabel as Cint64
        {
            label_type_string = "INDIRECTLY_CONNECTED_NOMINAL_INDIVIDUAL_SET_LABEL".to_string();
        } else if label_type == LabelCacheItemType::NeighbourInstantiatedRoleSetLabel as Cint64 {
            label_type_string = "NEIGHBOUR_INSTANTIATED_ROLE_SET_LABEL".to_string();
        } else if label_type
            == LabelCacheItemType::DeterministicCombinedDataInstantiatedRoleSetLabel as Cint64
        {
            label_type_string =
                "DETERMINISTIC_COMBINED_DATA_INSTANTIATED_ROLE_SET_LABEL".to_string();
        } else if label_type
            == LabelCacheItemType::NondeterministicCombinedDataInstantiatedRoleSetLabel as Cint64
        {
            label_type_string =
                "NONDETERMINISTIC_COMBINED_DATA_INSTANTIATED_ROLE_SET_LABEL".to_string();
        }
        label_type_string
    }

    /// Port of `CBackendRepresentativeMemoryCache::getRepresentativeCacheString` (no-arg).
    ///
    /// Faithful driver over the real `ontology_identifier_data_hash` field: emits an
    /// "Ontology: <id>" banner per ontology and appends that ontology's stringified
    /// cache (via the `_for_ontology` overload).
    /// KONCLUDE-PORT-NOTE[api]: `CCACHINGHASH` preserves insertion order; the Rust
    /// `HashMap` iteration order differs — irrelevant for a debug dump.
    pub fn get_representative_cache_string(&self) -> Vec<String> {
        let mut cache_string_list: Vec<String> = Vec::new();
        for (ont_id, ontology_data) in &self.ontology_identifier_data_hash {
            cache_string_list.push(format!("Ontology: {}\r\n\r\n\r\n", ont_id));
            let ontology_id_data_string_list =
                self.get_representative_cache_string_for_ontology(*ontology_data);
            cache_string_list.extend(ontology_id_data_string_list);
            cache_string_list.push("\r\n\r\n\r\n\r\n\r\n\r\n".to_string());
        }
        cache_string_list
    }

    /// Port of `CBackendRepresentativeMemoryCache::debugCheckWriteMaxSameMergedIndividualsToFile`.
    ///
    /// W6-DEFER[api]: walks the `DETERMINISTIC_SAME_INDIVIDUAL_SET_LABEL` signature
    /// hash to find the label item with the largest same-as-merged value count, then
    /// resolves each merged individual's IRI (via `mDebugOntology` ABox, opaque) and
    /// diffs the name set against a previously-saved file. Pure debugging instrumentation;
    /// derefs `OntologyData` signature hashes + the opaque debug ontology. Restore on reconcile.
    pub fn debug_check_write_max_same_merged_individuals_to_file(
        &self,
        ontology_data: OntologyDataId,
    ) {
        // W6-DEFER[api]: facade-arena deref + opaque mDebugOntology ABox (see doc-comment).
        let _ = ontology_data;
    }

    /// Port of `CBackendRepresentativeMemoryCache::getRepresentativeCacheString`
    /// (the `CBackendRepresentativeMemoryCacheOntologyData*` overload).
    ///
    /// KONCLUDE-PORT-NOTE[overload]: Rust cannot overload; this variant takes the
    /// `_for_ontology` suffix (the no-arg variant keeps the bare name).
    ///
    /// W6-DEFER[api]: builds the full per-ontology debug dump — every label item per
    /// signature hash (with cache values + cardinality extension data) plus every
    /// individual's association debug string (via `get_individual_association_debug_string`)
    /// and a statistics block. Derefs the `OntologyData` signature hashes, label items,
    /// the individual-association-data vector, and cardinality extension data. Restore on
    /// reconcile; returns the assembled string list (empty until the arenas are wired).
    pub fn get_representative_cache_string_for_ontology(
        &self,
        ontology_data: OntologyDataId,
    ) -> Vec<String> {
        // W6-DEFER[api]: facade-arena deref over labels + individuals (see doc-comment).
        let _ = ontology_data;
        Vec::new()
    }

    /// Port of `CBackendRepresentativeMemoryCache::getIndividualAssociationDebugString`.
    ///
    /// W6-DEFER[api]: assembles one individual's full debug string — update ids, the
    /// saturated/propagated/handled/involved status flags, representative + deterministic
    /// same-individual ids, every associated label, the role-set neighbour array (with
    /// per-neighbour clash/propagation annotations), indirectly-connected nominal data,
    /// and the memory-management context. Derefs `IndividualAssociationData`, its
    /// `IndividualRoleSetNeighbourArray`, and the `OntologyData` vectors/hashes. Restore
    /// on reconcile; returns the per-individual string (empty until arenas are wired).
    pub fn get_individual_association_debug_string(
        &self,
        indi_id: Cint64,
        indi_ass_data: IndividualAssociationDataId,
        ontology_data: OntologyDataId,
        prev_tab: Cint64,
    ) -> String {
        // W6-DEFER[api]: facade-arena deref over the association data (see doc-comment).
        let _ = (indi_id, indi_ass_data, ontology_data, prev_tab);
        String::new()
    }

    // =======================================================================
    // Debug consistency checks (KONCLUDE_CACHE_DEBUGGING_DATA_GENERATION-gated)
    // =======================================================================

    /// Port of `CBackendRepresentativeMemoryCache::debugCheckPropagationCutRemainingNeighbours`.
    ///
    /// KONCLUDE-PORT-NOTE[macro]: the entire body is inside
    /// `#ifdef KONCLUDE_CACHE_DEBUGGING_DATA_GENERATION` — in the normal build it is
    /// `bool error = false; return error;`. Ported faithfully for the normal build; the
    /// gated body (diffing prev/new neighbour array positions) is debug-only and omitted.
    pub fn debug_check_propagation_cut_remaining_neighbours(
        &self,
        indi_ass_data: IndividualAssociationDataId,
        ontology_data: OntologyDataId,
    ) -> bool {
        let error = false;
        // KONCLUDE_CACHE_DEBUGGING_DATA_GENERATION-gated body omitted (build-flag only).
        let _ = (indi_ass_data, ontology_data);
        error
    }

    /// Port of `CBackendRepresentativeMemoryCache::debugCheckSingleNeighbourInvolvedOccurrences`.
    ///
    /// KONCLUDE-PORT-NOTE[macro]: entire body is `#ifdef KONCLUDE_CACHE_DEBUGGING_DATA_GENERATION`;
    /// normal build is `bool error = false; return error;`. Gated body omitted.
    pub fn debug_check_single_neighbour_involved_occurrences(
        &self,
        indi_ass_data: IndividualAssociationDataId,
        ontology_data: OntologyDataId,
    ) -> bool {
        let error = false;
        // KONCLUDE_CACHE_DEBUGGING_DATA_GENERATION-gated body omitted (build-flag only).
        let _ = (indi_ass_data, ontology_data);
        error
    }

    /// Port of `CBackendRepresentativeMemoryCache::debugCheckCorrectNeighbourOccurrence`.
    ///
    /// KONCLUDE-PORT-NOTE[macro]: entire body is `#ifdef KONCLUDE_CACHE_DEBUGGING_DATA_GENERATION`;
    /// normal build is `bool missingOccurrence = false; return missingOccurrence;`.
    /// Gated body (LUBM-specific neighbour-name expectations + `s1/s2/s3` toggles) omitted.
    pub fn debug_check_correct_neighbour_occurrence(
        &self,
        indi_ass_data: IndividualAssociationDataId,
        ontology_data: OntologyDataId,
    ) -> bool {
        let missing_occurrence = false;
        // KONCLUDE_CACHE_DEBUGGING_DATA_GENERATION-gated body omitted (build-flag only).
        let _ = (indi_ass_data, ontology_data);
        missing_occurrence
    }

    /// Port of `CBackendRepresentativeMemoryCache::debugCheckNeighoursCorrectlyCounted`.
    pub fn debug_check_neighours_correctly_counted(
        &self,
        indi_ass_data: IndividualAssociationDataId,
        ontology_data: OntologyDataId,
        cache_context: &CacheContext,
    ) -> bool {
        let _ = ontology_data;
        if indi_ass_data.is_some() {
            let role_set_neighbour_array = cache_context
                .individual_assoc_data(indi_ass_data)
                .get_role_set_neighbour_array();
            if role_set_neighbour_array.is_some() {
                let role_set_neighbour_array =
                    cache_context.individual_role_set_neighbour_array(role_set_neighbour_array);
                let index_data = role_set_neighbour_array.get_index_data();
                let array_size = cache_context
                    .label_cache_item_ext_data(index_data)
                    .get_array_size();
                for i in 0..array_size {
                    let data_id = role_set_neighbour_array.at(i);
                    let data = cache_context.individual_role_set_neighbour_data(data_id);
                    let indi_linker = data.get_individual_id_linker();
                    let mut count = 0;
                    if indi_linker.is_empty() {
                        let debug = false;
                        if debug {
                            // C++ would call writeStringifiedRepresentativeCacheToFile().
                        }
                    }
                    if !indi_linker.is_empty() {
                        count = indi_linker.len() as Cint64;
                    }
                    if count != data.get_individual_count() {
                        let debug = false;
                        if debug {
                            // C++ would call writeStringifiedRepresentativeCacheToFile().
                        }
                        return false;
                    }
                }
            }
        }
        true
    }

    // =======================================================================
    // Facade utilities
    // =======================================================================

    /// Port of `CBackendRepresentativeMemoryCache::checkAssociationComplete`.
    pub fn check_association_complete(
        &mut self,
        ontology_data: OntologyDataId,
        force_completion: bool,
        cache_context: &mut CacheContext,
    ) {
        if ontology_data.is_none() {
            return;
        }
        let should_complete = {
            let data = cache_context.ontology_data(ontology_data);
            (data.get_incompletely_handled_individual_id_count() <= 0 || force_completion)
                && !data.is_association_completed()
                && data.is_first_incompletely_handled_individuals_retrieved()
        };
        if should_complete {
            let ontology_identifier = {
                let data = cache_context.ontology_data_mut(ontology_data);
                let ontology_identifier = data.get_ontology_identifer();
                data.set_association_completed(true);
                // mFixedOntologyIdentifierDataHashLock.lockForWrite(); [threading]
                data.inc_usage_count(1);
                ontology_identifier
            };
            self.fixed_ontology_identifier_data_hash
                .insert(ontology_identifier, ontology_data);
            // mFixedOntologyIdentifierDataHashLock.unlock(); [threading]

            {
                let data = cache_context.ontology_data_mut(ontology_data);
                let _ = data.get_max_stored_indvidual_id();
                let _ = data.get_next_entry_id(false);
            }

            if self.conf_late_individual_label_association_indexing {
                self.index_individual_label_associations(ontology_data, cache_context);
            }

            if self.conf_debug_write_representative_cache {
                self.write_stringified_representative_cache_to_file();
            }
        }
    }

    /// Port of `CBackendRepresentativeMemoryCache::debugTestingPrioritizedExpansionLinkDuplicates`.
    pub fn debug_testing_prioritized_expansion_link_duplicates(
        &self,
        testing_array: IndividualRoleSetNeighbourArrayId,
        prop_mark_label_item: LabelCacheItemId,
        cache_context: &CacheContext,
    ) -> bool {
        if testing_array.is_some() {
            let testing_array_ref =
                cache_context.individual_role_set_neighbour_array(testing_array);
            let testing_array_index_data = testing_array_ref.get_index_data();
            if testing_array_index_data.is_some() {
                let testing_prio_prop_mark_index = cache_context
                    .label_cache_item_ext_data(testing_array_index_data)
                    .get_index(prop_mark_label_item);
                if testing_prio_prop_mark_index >= 0 {
                    let mut neighbour_indi_id_set = std::collections::HashSet::new();
                    let data_id = testing_array_ref.at(testing_prio_prop_mark_index);
                    if data_id.is_some() {
                        cache_context
                            .individual_role_set_neighbour_data(data_id)
                            .visit_neighbour_individual_ids(
                                &mut |id| {
                                    if neighbour_indi_id_set.contains(&id) {
                                        let debug = true;
                                        let _ = debug;
                                    } else {
                                        neighbour_indi_id_set.insert(id);
                                    }
                                    true
                                },
                                cache_context,
                            );
                    }
                }
            }
        }
        true
    }

    /// Port of `CBackendRepresentativeMemoryCache::copyNeighbourIndividualIdLinkers`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: the C++ argument is a chain head; in this
    /// port, neighbour-id linker chains are represented as head-front slices.
    /// The `context` allocation handle is preserved in the signature but arena
    /// allocation goes through `CacheContext`.
    pub fn copy_neighbour_individual_id_linkers(
        &mut self,
        indi_id_linker: &[IndividualRoleSetNeighbourIndividualIdLinkerId],
        context: Cint64,
        loc_association_data: IndividualAssociationDataId,
        pos: Cint64,
        cache_context: &mut CacheContext,
    ) -> Vec<IndividualRoleSetNeighbourIndividualIdLinkerId> {
        let _ = (context, loc_association_data, pos);
        let mut first_new_indi_id_linker = Vec::new();
        let mut copied_linker_count = 0;
        for indi_id_linker_it in indi_id_linker.iter().copied() {
            let neighbour_id = cache_context
                .individual_role_set_neighbour_id_linker(indi_id_linker_it)
                .get_individual_id();
            let mut new_linker = IndividualRoleSetNeighbourIndividualIdLinker::new();
            new_linker.init_individual_id_linker(neighbour_id);
            let new_linker =
                cache_context.alloc_individual_role_set_neighbour_id_linker(new_linker);
            self.stat_individual_association_separate_memory_managment_neighbour_link_copying_count +=
                1;
            copied_linker_count += 1;
            first_new_indi_id_linker.push(new_linker);
        }
        let _ = copied_linker_count;
        first_new_indi_id_linker
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cached_ontology(ctx: &mut CacheContext, ontology: OntologyData) -> OntologyDataId {
        ctx.alloc_ontology_data(ontology)
    }

    fn role_cache_value(
        role: Cint64,
        inversed: bool,
        assertion: bool,
        nominal: bool,
        nondeterministic: bool,
    ) -> CacheValue {
        crate::konclude_ht::cache::backend::BackendRepresentativeMemoryCacheReader::new()
            .get_cache_value_role_qualified(role, inversed, assertion, nominal, nondeterministic)
    }

    fn role_label_from_values(ctx: &mut CacheContext, values: &[CacheValue]) -> LabelCacheItemId {
        let entries: Vec<_> = values
            .iter()
            .copied()
            .map(|value| (value.get_tag(), value))
            .collect();
        role_label_from_entries(ctx, &entries)
    }

    fn role_label_from_entries(
        ctx: &mut CacheContext,
        entries: &[(Cint64, CacheValue)],
    ) -> LabelCacheItemId {
        let mut label = LabelCacheItem::new(INVALID);
        label.cache_item_type = LabelCacheItemType::NeighbourInstantiatedRoleSetLabel;
        let mut chain = Vec::new();
        for &(hash_tag, value) in entries.iter().rev() {
            let mut linker = LabelValueLinker::new();
            linker.init_label_value_linker(value);
            let linker = ctx.alloc_label_value_linker(linker);
            label.tag_value_hash.insert(hash_tag, linker);
            chain.insert(0, linker);
        }
        label.add_cache_value_linker(&chain);
        ctx.alloc_label_cache_item(label)
    }

    #[test]
    fn backend_role_neighbour_link_label_compatibility_matches_konclude() {
        let mut ctx = CacheContext::new();
        let cache = BackendRepresentativeMemoryCache::default();

        let prev = role_label_from_values(
            &mut ctx,
            &[
                role_cache_value(10, false, false, false, true),
                role_cache_value(20, true, false, false, false),
            ],
        );
        let compatible_new = role_label_from_values(
            &mut ctx,
            &[
                role_cache_value(10, false, false, false, false),
                role_cache_value(20, true, false, false, false),
            ],
        );
        assert!(cache.is_role_neighbour_link_label_item_compatibility(prev, compatible_new, &ctx,));

        let missing_tag = role_label_from_values(
            &mut ctx,
            &[
                role_cache_value(10, false, false, false, false),
                role_cache_value(30, true, false, false, false),
            ],
        );
        assert!(!cache.is_role_neighbour_link_label_item_compatibility(prev, missing_tag, &ctx,));

        let deterministic_prev = role_label_from_values(
            &mut ctx,
            &[role_cache_value(40, false, false, false, false)],
        );
        let nondeterministic_new =
            role_label_from_values(&mut ctx, &[role_cache_value(40, false, false, false, true)]);
        assert!(!cache.is_role_neighbour_link_label_item_compatibility(
            deterministic_prev,
            nondeterministic_new,
            &ctx,
        ));

        let inverted_value = role_cache_value(50, true, false, false, false);
        let prev_inverse_mismatch = role_label_from_entries(&mut ctx, &[(50, inverted_value)]);
        let new_non_inverse = role_label_from_values(
            &mut ctx,
            &[role_cache_value(50, false, false, false, false)],
        );
        assert!(!cache.is_role_neighbour_link_label_item_compatibility(
            prev_inverse_mismatch,
            new_non_inverse,
            &ctx,
        ));
    }

    fn deterministic_same_update_association(
        ctx: &mut CacheContext,
        individual_id: Cint64,
        deterministic_same_id: Cint64,
        representative_same_id: Cint64,
        role_set_neighbour_array: IndividualRoleSetNeighbourArrayId,
        label: LabelCacheItemId,
        incompletely_marked: bool,
    ) -> IndividualAssociationDataId {
        let mut data = IndividualAssociationData::default();
        data.init_association_data_for_id(individual_id)
            .set_deterministic_same_individual_id(deterministic_same_id)
            .set_representative_same_individual_id(representative_same_id)
            .set_role_set_neighbour_array(role_set_neighbour_array)
            .set_label_cache_entry(LabelCacheItemType::FullConceptSetLabel as Cint64, label)
            .set_incompletely_marked(incompletely_marked);
        ctx.alloc_individual_assoc_data(data)
    }

    #[test]
    fn backend_check_requires_deterministic_same_update_matches_konclude() {
        let mut ctx = CacheContext::new();
        let cache = BackendRepresentativeMemoryCache::default();
        let label = ctx.alloc_label_cache_item(LabelCacheItem::default());
        let other_label = ctx.alloc_label_cache_item(LabelCacheItem::default());
        let array =
            ctx.alloc_individual_role_set_neighbour_array(IndividualRoleSetNeighbourArray::new());
        let other_array =
            ctx.alloc_individual_role_set_neighbour_array(IndividualRoleSetNeighbourArray::new());
        let ontology = cached_ontology(&mut ctx, OntologyData::new());

        let target = deterministic_same_update_association(&mut ctx, 9, 9, 9, array, label, false);
        let matching =
            deterministic_same_update_association(&mut ctx, 5, 9, 9, array, label, false);
        assert!(
            !cache.check_requires_deterministic_same_as_association_update_installation(
                matching, 5, target, 9, ontology, &ctx,
            )
        );

        let det_id_changed =
            deterministic_same_update_association(&mut ctx, 5, 8, 9, array, label, false);
        assert!(
            cache.check_requires_deterministic_same_as_association_update_installation(
                det_id_changed,
                5,
                target,
                9,
                ontology,
                &ctx,
            )
        );

        let representative_changed =
            deterministic_same_update_association(&mut ctx, 5, 9, 8, array, label, false);
        assert!(
            cache.check_requires_deterministic_same_as_association_update_installation(
                representative_changed,
                5,
                target,
                9,
                ontology,
                &ctx,
            )
        );

        let array_changed =
            deterministic_same_update_association(&mut ctx, 5, 9, 9, other_array, label, false);
        assert!(
            cache.check_requires_deterministic_same_as_association_update_installation(
                array_changed,
                5,
                target,
                9,
                ontology,
                &ctx,
            )
        );

        let incomplete =
            deterministic_same_update_association(&mut ctx, 5, 9, 9, array, label, true);
        assert!(
            cache.check_requires_deterministic_same_as_association_update_installation(
                incomplete, 5, target, 9, ontology, &ctx,
            )
        );

        let label_changed =
            deterministic_same_update_association(&mut ctx, 5, 9, 9, array, other_label, false);
        assert!(
            cache.check_requires_deterministic_same_as_association_update_installation(
                label_changed,
                5,
                target,
                9,
                ontology,
                &ctx,
            )
        );
    }

    #[test]
    fn backend_update_indexed_association_count_moves_between_labels() {
        let mut ctx = CacheContext::new();
        let prev_label = ctx.alloc_label_cache_item(LabelCacheItem::default());
        let new_label = ctx.alloc_label_cache_item(LabelCacheItem::default());
        ctx.label_cache_item_mut(prev_label)
            .inc_individual_association_count(1);

        let loc_association = association_with_label(
            &mut ctx,
            5,
            LabelCacheItemType::FullConceptSetLabel,
            new_label,
        );
        let ontology = cached_ontology(&mut ctx, OntologyData::new());
        let mut cache = BackendRepresentativeMemoryCache::default();
        let prev_extension =
            cache.get_individual_associations_extension_data(prev_label, ontology, &mut ctx);
        ctx.label_cache_item_ext_data_mut(prev_extension)
            .add_individual_id_association(5, false);

        assert!(cache.update_indexed_association_count(
            loc_association,
            prev_label,
            LabelCacheItemType::FullConceptSetLabel as Cint64,
            ontology,
            &mut ctx,
        ));

        assert_eq!(
            ctx.label_cache_item(prev_label)
                .get_individual_association_count(),
            0
        );
        assert_eq!(
            ctx.label_cache_item(new_label)
                .get_individual_association_count(),
            1
        );
        match ctx.label_cache_item_ext_data(prev_extension) {
            LabelCacheItemExtensionData::IndividualAssociationMap {
                base_indi_asso_map,
                same_indi_merged_asso_map,
                ..
            } => {
                assert!(base_indi_asso_map.is_empty());
                assert!(same_indi_merged_asso_map.is_empty());
            }
            _ => panic!("expected previous individual-association map"),
        }
        let new_extension = ctx
            .label_cache_item(new_label)
            .get_extension_data(LabelCacheItemExtensionType::IndividualAssociationMap as Cint64);
        match ctx.label_cache_item_ext_data(new_extension) {
            LabelCacheItemExtensionData::IndividualAssociationMap {
                base_indi_asso_map,
                same_indi_merged_asso_map,
                ..
            } => {
                assert_eq!(base_indi_asso_map, &vec![5]);
                assert!(same_indi_merged_asso_map.is_empty());
            }
            _ => panic!("expected new individual-association map"),
        }
    }

    #[test]
    fn backend_update_indexed_association_count_for_association_data_retracks_same_merge_change() {
        let mut ctx = CacheContext::new();
        let label = ctx.alloc_label_cache_item(LabelCacheItem::default());
        ctx.label_cache_item_mut(label)
            .inc_individual_association_count(1);

        let mut previous = IndividualAssociationData::default();
        previous
            .init_association_data_for_id(7)
            .set_representative_same_individual_id(99)
            .set_label_cache_entry(LabelCacheItemType::FullConceptSetLabel as Cint64, label);
        let previous = ctx.alloc_individual_assoc_data(previous);

        let mut local = IndividualAssociationData::default();
        local
            .init_association_data_for_id(7)
            .set_label_cache_entry(LabelCacheItemType::FullConceptSetLabel as Cint64, label);
        let local = ctx.alloc_individual_assoc_data(local);

        let ontology = cached_ontology(&mut ctx, OntologyData::new());
        let mut cache = BackendRepresentativeMemoryCache::default();
        let extension = cache.get_individual_associations_extension_data(label, ontology, &mut ctx);
        ctx.label_cache_item_ext_data_mut(extension)
            .add_individual_id_association(7, true);

        assert!(cache.update_indexed_association_count_for_association_data(
            local,
            previous,
            LabelCacheItemType::FullConceptSetLabel as Cint64,
            ontology,
            &mut ctx,
        ));

        assert_eq!(
            ctx.label_cache_item(label)
                .get_individual_association_count(),
            1
        );
        match ctx.label_cache_item_ext_data(extension) {
            LabelCacheItemExtensionData::IndividualAssociationMap {
                base_indi_asso_map,
                same_indi_merged_asso_map,
                ..
            } => {
                assert_eq!(base_indi_asso_map, &vec![7]);
                assert!(same_indi_merged_asso_map.is_empty());
            }
            _ => panic!("expected individual-association map"),
        }
    }

    #[test]
    fn backend_minimum_slot_referring_recomputation_id_returns_empty_max() {
        let mut ctx = CacheContext::new();
        let ontology = cached_ontology(&mut ctx, OntologyData::new());
        let cache = BackendRepresentativeMemoryCache::default();

        assert_eq!(
            cache.get_minimum_slot_referrering_installed_valid_recomputation_id(ontology, &ctx),
            Cint64::MAX
        );
        assert_eq!(
            cache.get_minimum_slot_referrering_installed_valid_recomputation_id(
                OntologyDataId::NONE,
                &ctx
            ),
            Cint64::MAX
        );
    }

    #[test]
    fn backend_minimum_slot_referring_recomputation_id_scans_slot_chain() {
        let mut ctx = CacheContext::new();
        let mut query_ontology = OntologyData::new();
        query_ontology.init_ontology_data(55, false);
        let query_ontology = cached_ontology(&mut ctx, query_ontology);

        let mut older = OntologyData::new();
        older
            .init_ontology_data(55, false)
            .set_minimum_valid_recomputation_id(9);
        let older = cached_ontology(&mut ctx, older);

        let mut newer = OntologyData::new();
        newer
            .init_ontology_data(55, false)
            .set_minimum_valid_recomputation_id(3);
        let newer = cached_ontology(&mut ctx, newer);

        let mut other = OntologyData::new();
        other
            .init_ontology_data(77, false)
            .set_minimum_valid_recomputation_id(1);
        let other = cached_ontology(&mut ctx, other);

        let mut first_slot = super::super::backend::BackendRepresentativeMemoryCacheSlotItem::new();
        first_slot
            .set_ontology_identifier_data_hash([(55, older), (77, other)].into_iter().collect());
        let first_slot = ctx.alloc_backend_slot_item(first_slot);

        let mut second_slot =
            super::super::backend::BackendRepresentativeMemoryCacheSlotItem::new();
        second_slot.set_ontology_identifier_data_hash([(55, newer)].into_iter().collect());
        let second_slot = ctx.alloc_backend_slot_item(second_slot);

        let mut cache = BackendRepresentativeMemoryCache::default();
        cache.slot_linker = vec![first_slot, second_slot];

        assert_eq!(
            cache.get_minimum_slot_referrering_installed_valid_recomputation_id(
                query_ontology,
                &ctx
            ),
            3
        );
    }

    #[test]
    fn backend_create_cache_reader_allocates_and_prepends_reader() {
        let mut ctx = CacheContext::new();
        let mut cache = BackendRepresentativeMemoryCache::default();

        let first = cache.create_cache_reader(&mut ctx);
        let second = cache.create_cache_reader(&mut ctx);

        assert!(first.is_some());
        assert!(second.is_some());
        assert_ne!(first, second);
        assert_eq!(cache.reader_linker, vec![second, first]);
        assert!(ctx
            .backend_cache_reader(first)
            .fixed_ontology_data
            .is_none());
        assert!(ctx.backend_cache_reader(second).ontology_data.is_none());
    }

    #[test]
    fn backend_create_ontology_fixed_cache_reader_pins_fixed_ontology_data() {
        let mut ctx = CacheContext::new();
        let ontology = cached_ontology(&mut ctx, OntologyData::new());
        let mut cache = BackendRepresentativeMemoryCache::default();
        cache
            .fixed_ontology_identifier_data_hash
            .insert(77, ontology);

        let reader = cache.create_ontology_fixed_cache_reader(77, &mut ctx);

        assert!(reader.is_some());
        assert!(cache.reader_linker.is_empty());
        assert_eq!(
            ctx.backend_cache_reader(reader).fixed_ontology_data,
            ontology
        );
        assert_eq!(ctx.backend_cache_reader(reader).ontology_data, ontology);
        assert_eq!(ctx.ontology_data(ontology).get_usage_count(), 1);
    }

    #[test]
    fn backend_create_ontology_fixed_cache_reader_allows_missing_ontology() {
        let mut ctx = CacheContext::new();
        let mut cache = BackendRepresentativeMemoryCache::default();

        let reader = cache.create_ontology_fixed_cache_reader(999, &mut ctx);

        assert!(reader.is_some());
        assert!(ctx
            .backend_cache_reader(reader)
            .fixed_ontology_data
            .is_none());
        assert!(ctx.backend_cache_reader(reader).ontology_data.is_none());
    }

    #[test]
    fn backend_basic_precomputation_activation_matches_ratio_guard() {
        let mut ctx = CacheContext::new();
        let mut ontology = OntologyData::new();
        ontology
            .set_incompletely_handled_individual_id_count(3)
            .inc_individual_association_data_direct_update_count(100)
            .inc_individual_association_merging_count(6);
        let ontology_id = cached_ontology(&mut ctx, ontology);
        let cache = BackendRepresentativeMemoryCache::default();

        assert!(cache.check_basic_precompuation_mode_activation(ontology_id, &ctx));
    }

    #[test]
    fn backend_basic_precomputation_activation_rejects_below_threshold() {
        let mut ctx = CacheContext::new();
        let mut ontology = OntologyData::new();
        ontology
            .set_incompletely_handled_individual_id_count(3)
            .inc_individual_association_data_direct_update_count(100)
            .inc_individual_association_merging_count(5);
        let ontology_id = cached_ontology(&mut ctx, ontology);
        let cache = BackendRepresentativeMemoryCache::default();

        assert!(!cache.check_basic_precompuation_mode_activation(ontology_id, &ctx));
    }

    #[test]
    fn backend_basic_precomputation_activation_honors_outer_guards() {
        let mut ctx = CacheContext::new();
        let mut ontology = OntologyData::new();
        ontology
            .set_incompletely_handled_individual_id_count(3)
            .inc_individual_association_data_direct_update_count(100)
            .inc_individual_association_merging_count(6)
            .set_basic_precomputation_mode_activation(true);
        let ontology_id = cached_ontology(&mut ctx, ontology);
        let cache = BackendRepresentativeMemoryCache::default();

        assert!(!cache.check_basic_precompuation_mode_activation(ontology_id, &ctx));
        assert!(!cache.check_basic_precompuation_mode_activation(OntologyDataId::NONE, &ctx));
    }

    #[test]
    fn backend_activate_basic_precomputation_mode_snapshots_association_vector() {
        let mut ctx = CacheContext::new();
        let first = ctx.alloc_individual_assoc_data(IndividualAssociationData::default());
        let second = ctx.alloc_individual_assoc_data(IndividualAssociationData::default());
        let mut ontology = OntologyData::new();
        ontology
            .set_individual_id_assoiation_data_vector_size(3)
            .set_individual_id_assoiation_data_vector(
                3,
                vec![first, second, IndividualAssociationDataId::NONE],
            )
            .inc_individual_association_data_direct_update_count(11)
            .inc_individual_association_merging_count(2);
        let ontology_id = cached_ontology(&mut ctx, ontology);
        let mut cache = BackendRepresentativeMemoryCache::default();

        assert!(cache.activate_basic_precompuation_mode(ontology_id, &mut ctx));
        let ontology = ctx.ontology_data(ontology_id);
        assert!(ontology.is_basic_precomputation_mode());
        assert!(ontology.has_basic_precomputation_mode_activation());
        assert_eq!(
            ontology.get_basic_precomputation_individual_id_assoiation_data_vector(),
            &[first, second, IndividualAssociationDataId::NONE]
        );
        assert_eq!(
            ontology.get_basic_precomputation_individual_id_assoiation_data_vector_size(),
            3
        );
    }

    #[test]
    fn backend_activate_basic_precomputation_mode_rejects_repeated_activation() {
        let mut ctx = CacheContext::new();
        let mut ontology = OntologyData::new();
        ontology.set_basic_precomputation_mode_activation(true);
        let ontology_id = cached_ontology(&mut ctx, ontology);
        let mut cache = BackendRepresentativeMemoryCache::default();

        assert!(!cache.activate_basic_precompuation_mode(ontology_id, &mut ctx));
        assert!(!cache.activate_basic_precompuation_mode(OntologyDataId::NONE, &mut ctx));
    }

    fn association_with_label(
        ctx: &mut CacheContext,
        individual_id: Cint64,
        label_type: LabelCacheItemType,
        label: LabelCacheItemId,
    ) -> IndividualAssociationDataId {
        let mut association = IndividualAssociationData::default();
        association
            .init_association_data_for_id(individual_id)
            .set_label_cache_entry(label_type as Cint64, label);
        ctx.alloc_individual_assoc_data(association)
    }

    #[test]
    fn backend_get_individual_associations_extension_data_lazily_installs_map() {
        let mut ctx = CacheContext::new();
        let label = ctx.alloc_label_cache_item(LabelCacheItem::default());
        let ontology = cached_ontology(&mut ctx, OntologyData::new());
        let mut cache = BackendRepresentativeMemoryCache::default();

        let extension = cache.get_individual_associations_extension_data(label, ontology, &mut ctx);

        assert!(extension.is_some());
        assert_eq!(
            ctx.label_cache_item(label).get_extension_data(
                LabelCacheItemExtensionType::IndividualAssociationMap as Cint64
            ),
            extension
        );
        assert!(matches!(
            ctx.label_cache_item_ext_data(extension),
            LabelCacheItemExtensionData::IndividualAssociationMap { .. }
        ));
    }

    #[test]
    fn backend_index_individual_label_associations_populates_required_label_maps() {
        let mut ctx = CacheContext::new();
        let tracked_label = ctx.alloc_label_cache_item(LabelCacheItem::default());
        let untracked_label = ctx.alloc_label_cache_item(LabelCacheItem::default());
        let first = association_with_label(
            &mut ctx,
            1,
            LabelCacheItemType::FullConceptSetLabel,
            tracked_label,
        );
        let second = association_with_label(
            &mut ctx,
            2,
            LabelCacheItemType::FullConceptSetLabel,
            tracked_label,
        );
        let _third_untracked = association_with_label(
            &mut ctx,
            3,
            LabelCacheItemType::DeterministicConceptSetLabel,
            untracked_label,
        );
        let mut ontology = OntologyData::new();
        ontology
            .set_individual_id_assoiation_data_vector_size(3)
            .update_max_stored_indvidual_id(2)
            .set_individual_id_assoiation_data_vector(
                3,
                vec![first, second, IndividualAssociationDataId::NONE],
            );
        let ontology = cached_ontology(&mut ctx, ontology);
        let mut cache = BackendRepresentativeMemoryCache::default();

        cache.index_individual_label_associations(ontology, &mut ctx);

        let extension = ctx
            .label_cache_item(tracked_label)
            .get_extension_data(LabelCacheItemExtensionType::IndividualAssociationMap as Cint64);
        match ctx.label_cache_item_ext_data(extension) {
            LabelCacheItemExtensionData::IndividualAssociationMap {
                base_indi_asso_map,
                same_indi_merged_asso_map,
                ..
            } => {
                assert_eq!(base_indi_asso_map, &vec![1, 2]);
                assert!(same_indi_merged_asso_map.is_empty());
            }
            _ => panic!("expected individual-association map extension"),
        }
        assert!(ctx
            .label_cache_item(untracked_label)
            .get_extension_data(LabelCacheItemExtensionType::IndividualAssociationMap as Cint64)
            .is_none());
        assert!(ctx
            .ontology_data(ontology)
            .is_individual_label_association_indexed());
    }

    #[test]
    fn backend_get_individual_neighbour_array_index_extension_data_lazily_installs_index() {
        let mut ctx = CacheContext::new();
        let label = ctx.alloc_label_cache_item(LabelCacheItem::default());
        let ontology = cached_ontology(&mut ctx, OntologyData::new());
        let mut cache = BackendRepresentativeMemoryCache::default();

        let extension =
            cache.get_individual_neighbour_array_index_extension_data(label, ontology, &mut ctx);

        assert!(extension.is_some());
        assert_eq!(
            ctx.label_cache_item(label).get_extension_data(
                LabelCacheItemExtensionType::IndividualNeighbourArrayIndex as Cint64
            ),
            extension
        );
        match ctx.label_cache_item_ext_data(extension) {
            LabelCacheItemExtensionData::NeighbourArrayIndex {
                combined_neighbour_role_set_label,
                array_size,
                ..
            } => {
                assert_eq!(*combined_neighbour_role_set_label, label);
                assert_eq!(*array_size, 0);
            }
            _ => panic!("expected neighbour-array index extension"),
        }
    }

    #[test]
    fn backend_get_individual_neighbour_array_index_extension_data_reuses_existing_index() {
        let mut ctx = CacheContext::new();
        let label = ctx.alloc_label_cache_item(LabelCacheItem::default());
        let existing =
            ctx.alloc_label_cache_item_ext_data(LabelCacheItemExtensionData::NeighbourArrayIndex {
                context: 0,
                combined_neighbour_role_set_label: label,
                array_size: 3,
                index_neighbour_role_set_label_array: Vec::new(),
                neighbour_role_set_label_index_hash: Default::default(),
            });
        ctx.label_cache_item_mut(label).set_extension_data(
            LabelCacheItemExtensionType::IndividualNeighbourArrayIndex as Cint64,
            existing,
        );
        let ontology = cached_ontology(&mut ctx, OntologyData::new());
        let mut cache = BackendRepresentativeMemoryCache::default();

        let extension =
            cache.get_individual_neighbour_array_index_extension_data(label, ontology, &mut ctx);

        assert_eq!(extension, existing);
        assert_eq!(ctx.label_cache_item_ext_data(extension).get_array_size(), 3);
    }

    fn role_label_with_cache_value(
        ctx: &mut CacheContext,
        tag: Cint64,
        identifier: CacheValueIdentifier,
    ) -> LabelCacheItemId {
        let cache_value = CacheValue::new_value(tag, tag, identifier);
        let mut linker = LabelValueLinker::new();
        linker.init_label_value_linker(cache_value);
        let linker = ctx.alloc_label_value_linker(linker);

        let mut label = LabelCacheItem::default();
        label.cache_item_type = LabelCacheItemType::NeighbourInstantiatedRoleSetLabel;
        label.add_cache_value_linker(&[linker]);
        ctx.alloc_label_cache_item(label)
    }

    fn neighbour_combination_label_with_refs(
        ctx: &mut CacheContext,
        labels: &[LabelCacheItemId],
    ) -> LabelCacheItemId {
        let mut label = LabelCacheItem::default();
        label.cache_item_type = LabelCacheItemType::NeighbourInstantiatedRoleSetCombinationLabel;
        let mut chain = Vec::new();
        for label_id in labels.iter().copied() {
            let cache_value = CacheValue::new_value(
                label_id.raw,
                label_id.raw,
                CacheValueIdentifier::CacheValueTagAndEntry,
            );
            let mut linker = LabelValueLinker::new();
            linker.init_label_value_linker(cache_value);
            chain.push(ctx.alloc_label_value_linker(linker));
        }
        label.add_cache_value_linker(&chain);
        ctx.alloc_label_cache_item(label)
    }

    #[test]
    fn backend_neighbour_array_index_initializer_builds_array_and_hash() {
        let mut ctx = CacheContext::new();
        let first_label = ctx.alloc_label_cache_item(LabelCacheItem::default());
        let second_label = ctx.alloc_label_cache_item(LabelCacheItem::default());
        let combined_label =
            neighbour_combination_label_with_refs(&mut ctx, &[first_label, second_label]);
        let ontology = cached_ontology(&mut ctx, OntologyData::new());
        let mut cache = BackendRepresentativeMemoryCache::default();

        let extension = cache.get_individual_neighbour_array_index_extension_data(
            combined_label,
            ontology,
            &mut ctx,
        );

        let extension_data = ctx.label_cache_item_ext_data(extension);
        assert_eq!(
            extension_data.get_combined_neighbour_role_set_label(),
            combined_label
        );
        assert_eq!(extension_data.get_array_size(), 2);
        assert_eq!(extension_data.get_neighbour_role_set_label(0), first_label);
        assert_eq!(extension_data.get_neighbour_role_set_label(1), second_label);
        assert_eq!(extension_data.get_index(first_label), 0);
        assert_eq!(extension_data.get_index(second_label), 1);
    }

    #[test]
    fn backend_get_neighbour_array_role_tag_resolving_extension_populates_from_index() {
        let mut ctx = CacheContext::new();
        let det_label =
            role_label_with_cache_value(&mut ctx, 101, CacheValueIdentifier::CacheValTagAndRole);
        let nondet_label = role_label_with_cache_value(
            &mut ctx,
            202,
            CacheValueIdentifier::CacheValTagAndNondeterministicInversedAssertedRole,
        );
        let combined_label = ctx.alloc_label_cache_item(LabelCacheItem::default());
        let index =
            ctx.alloc_label_cache_item_ext_data(LabelCacheItemExtensionData::NeighbourArrayIndex {
                context: 0,
                combined_neighbour_role_set_label: combined_label,
                array_size: 2,
                index_neighbour_role_set_label_array: vec![det_label, nondet_label],
                neighbour_role_set_label_index_hash: [(det_label, 0), (nondet_label, 1)]
                    .into_iter()
                    .collect(),
            });
        ctx.label_cache_item_mut(combined_label).set_extension_data(
            LabelCacheItemExtensionType::IndividualNeighbourArrayIndex as Cint64,
            index,
        );
        let ontology = cached_ontology(&mut ctx, OntologyData::new());
        let mut cache = BackendRepresentativeMemoryCache::default();

        let extension = cache.get_neighbour_array_role_tag_resolving_label_extension_data(
            combined_label,
            ontology,
            &mut ctx,
        );

        assert_eq!(
            ctx.label_cache_item(combined_label)
                .get_extension_data(LabelCacheItemExtensionType::TagResolvingHash as Cint64),
            extension
        );
        let det_linker = ctx
            .label_cache_item_ext_data(extension)
            .get_tag_label_resolving_data_linker(101);
        let nondet_linker = ctx
            .label_cache_item_ext_data(extension)
            .get_tag_label_resolving_data_linker(202);
        assert!(det_linker.is_some());
        assert!(nondet_linker.is_some());
        assert_eq!(
            ctx.tag_label_resolving_data_linker(det_linker)
                .get_label_cache_item(),
            det_label
        );
        assert_eq!(
            ctx.tag_label_resolving_data_linker(det_linker).get_index(),
            0
        );
        assert!(ctx
            .tag_label_resolving_data_linker(det_linker)
            .is_deterministic());
        assert_eq!(
            ctx.tag_label_resolving_data_linker(nondet_linker)
                .get_label_cache_item(),
            nondet_label
        );
        assert_eq!(
            ctx.tag_label_resolving_data_linker(nondet_linker)
                .get_index(),
            1
        );
        assert!(!ctx
            .tag_label_resolving_data_linker(nondet_linker)
            .is_deterministic());

        let reused = cache.get_neighbour_array_role_tag_resolving_label_extension_data(
            combined_label,
            ontology,
            &mut ctx,
        );
        assert_eq!(reused, extension);
    }

    #[test]
    fn backend_get_neighbour_array_role_tag_resolving_extension_builds_missing_index() {
        let mut ctx = CacheContext::new();
        let det_label =
            role_label_with_cache_value(&mut ctx, 301, CacheValueIdentifier::CacheValTagAndRole);
        let nondet_label = role_label_with_cache_value(
            &mut ctx,
            302,
            CacheValueIdentifier::CacheValTagAndNondeterministicNominalConnectedRole,
        );
        let combined_label =
            neighbour_combination_label_with_refs(&mut ctx, &[det_label, nondet_label]);
        let ontology = cached_ontology(&mut ctx, OntologyData::new());
        let mut cache = BackendRepresentativeMemoryCache::default();

        let extension = cache.get_neighbour_array_role_tag_resolving_label_extension_data(
            combined_label,
            ontology,
            &mut ctx,
        );

        let index_extension = ctx.label_cache_item(combined_label).get_extension_data(
            LabelCacheItemExtensionType::IndividualNeighbourArrayIndex as Cint64,
        );
        assert!(index_extension.is_some());
        assert_eq!(
            ctx.label_cache_item_ext_data(index_extension)
                .get_neighbour_role_set_label(0),
            det_label
        );
        assert_eq!(
            ctx.label_cache_item_ext_data(index_extension)
                .get_neighbour_role_set_label(1),
            nondet_label
        );
        let det_linker = ctx
            .label_cache_item_ext_data(extension)
            .get_tag_label_resolving_data_linker(301);
        let nondet_linker = ctx
            .label_cache_item_ext_data(extension)
            .get_tag_label_resolving_data_linker(302);
        assert!(ctx
            .tag_label_resolving_data_linker(det_linker)
            .is_deterministic());
        assert!(!ctx
            .tag_label_resolving_data_linker(nondet_linker)
            .is_deterministic());
    }

    fn neighbour_count_fixture(
        ctx: &mut CacheContext,
        stored_count: Cint64,
        linker_count: Cint64,
    ) -> IndividualAssociationDataId {
        let index_data =
            ctx.alloc_label_cache_item_ext_data(LabelCacheItemExtensionData::NeighbourArrayIndex {
                context: 0,
                combined_neighbour_role_set_label: LabelCacheItemId::NONE,
                array_size: 1,
                index_neighbour_role_set_label_array: Vec::new(),
                neighbour_role_set_label_index_hash: Default::default(),
            });

        let mut neighbour_data = IndividualRoleSetNeighbourData::new();
        neighbour_data.inc_individual_count(stored_count);
        let linkers: Vec<_> = (0..linker_count)
            .map(|i| {
                let mut linker = IndividualRoleSetNeighbourIndividualIdLinker::new();
                linker.init_individual_id_linker(i + 1);
                ctx.alloc_individual_role_set_neighbour_id_linker(linker)
            })
            .collect();
        neighbour_data.set_individual_id_linker(&linkers, false);
        let neighbour_data = ctx.alloc_individual_role_set_neighbour_data(neighbour_data);

        let mut array = IndividualRoleSetNeighbourArray::new();
        array.index_data = index_data;
        array.data_array.push(neighbour_data);
        let array = ctx.alloc_individual_role_set_neighbour_array(array);

        let mut association = IndividualAssociationData::default();
        association.set_role_set_neighbour_array(array);
        ctx.alloc_individual_assoc_data(association)
    }

    #[test]
    fn backend_debug_neighbour_count_accepts_matching_linker_count() {
        let mut ctx = CacheContext::new();
        let association = neighbour_count_fixture(&mut ctx, 2, 2);
        let cache = BackendRepresentativeMemoryCache::default();

        assert!(cache.debug_check_neighours_correctly_counted(
            association,
            OntologyDataId::NONE,
            &ctx
        ));
    }

    #[test]
    fn backend_debug_neighbour_count_rejects_mismatch() {
        let mut ctx = CacheContext::new();
        let association = neighbour_count_fixture(&mut ctx, 2, 1);
        let cache = BackendRepresentativeMemoryCache::default();

        assert!(!cache.debug_check_neighours_correctly_counted(
            association,
            OntologyDataId::NONE,
            &ctx
        ));
    }

    #[test]
    fn backend_debug_neighbour_count_accepts_missing_association() {
        let ctx = CacheContext::new();
        let cache = BackendRepresentativeMemoryCache::default();

        assert!(cache.debug_check_neighours_correctly_counted(
            IndividualAssociationDataId::NONE,
            OntologyDataId::NONE,
            &ctx
        ));
    }

    #[test]
    fn backend_check_association_complete_marks_and_publishes_ontology() {
        let mut ctx = CacheContext::new();
        let mut ontology = OntologyData::new();
        ontology
            .init_ontology_data(42, false)
            .set_first_incompletely_handled_individuals_retrieved(true);
        let ontology_id = cached_ontology(&mut ctx, ontology);
        let mut cache = BackendRepresentativeMemoryCache::default();

        cache.check_association_complete(ontology_id, false, &mut ctx);

        let ontology = ctx.ontology_data(ontology_id);
        assert!(ontology.is_association_completed());
        assert_eq!(ontology.usage_count, 1);
        assert_eq!(
            cache.fixed_ontology_identifier_data_hash.get(&42).copied(),
            Some(ontology_id)
        );
    }

    #[test]
    fn backend_check_association_complete_honors_retrieved_guard() {
        let mut ctx = CacheContext::new();
        let mut ontology = OntologyData::new();
        ontology.init_ontology_data(43, false);
        let ontology_id = cached_ontology(&mut ctx, ontology);
        let mut cache = BackendRepresentativeMemoryCache::default();

        cache.check_association_complete(ontology_id, false, &mut ctx);

        assert!(!ctx.ontology_data(ontology_id).is_association_completed());
        assert!(!cache.fixed_ontology_identifier_data_hash.contains_key(&43));
    }

    #[test]
    fn backend_check_association_complete_force_overrides_remaining_count() {
        let mut ctx = CacheContext::new();
        let mut ontology = OntologyData::new();
        ontology
            .init_ontology_data(44, false)
            .set_first_incompletely_handled_individuals_retrieved(true)
            .set_incompletely_handled_individual_id_count(7);
        let ontology_id = cached_ontology(&mut ctx, ontology);
        let mut cache = BackendRepresentativeMemoryCache::default();

        cache.check_association_complete(ontology_id, true, &mut ctx);

        assert!(ctx.ontology_data(ontology_id).is_association_completed());
        assert_eq!(
            cache.fixed_ontology_identifier_data_hash.get(&44).copied(),
            Some(ontology_id)
        );
    }

    fn prioritized_duplicate_fixture(
        ctx: &mut CacheContext,
        neighbour_ids: &[Cint64],
    ) -> (IndividualRoleSetNeighbourArrayId, LabelCacheItemId) {
        let prop_mark_label = ctx.alloc_label_cache_item(LabelCacheItem::default());
        let index_data =
            ctx.alloc_label_cache_item_ext_data(LabelCacheItemExtensionData::NeighbourArrayIndex {
                context: 0,
                combined_neighbour_role_set_label: LabelCacheItemId::NONE,
                array_size: 1,
                index_neighbour_role_set_label_array: vec![prop_mark_label],
                neighbour_role_set_label_index_hash: [(prop_mark_label, 0)].into_iter().collect(),
            });

        let mut neighbour_data = IndividualRoleSetNeighbourData::new();
        let linkers: Vec<_> = neighbour_ids
            .iter()
            .map(|id| {
                let mut linker = IndividualRoleSetNeighbourIndividualIdLinker::new();
                linker.init_individual_id_linker(*id);
                ctx.alloc_individual_role_set_neighbour_id_linker(linker)
            })
            .collect();
        neighbour_data.set_individual_id_linker(&linkers, true);
        let neighbour_data = ctx.alloc_individual_role_set_neighbour_data(neighbour_data);

        let mut array = IndividualRoleSetNeighbourArray::new();
        array.index_data = index_data;
        array.data_array.push(neighbour_data);
        (
            ctx.alloc_individual_role_set_neighbour_array(array),
            prop_mark_label,
        )
    }

    #[test]
    fn backend_debug_prioritized_duplicate_walks_indexed_neighbour_ids() {
        let mut ctx = CacheContext::new();
        let (testing_array, prop_mark_label) = prioritized_duplicate_fixture(&mut ctx, &[7, 8, 7]);
        let cache = BackendRepresentativeMemoryCache::default();

        assert!(cache.debug_testing_prioritized_expansion_link_duplicates(
            testing_array,
            prop_mark_label,
            &ctx
        ));
    }

    #[test]
    fn backend_debug_prioritized_duplicate_accepts_missing_index() {
        let mut ctx = CacheContext::new();
        let (testing_array, _) = prioritized_duplicate_fixture(&mut ctx, &[1, 2]);
        let other_label = ctx.alloc_label_cache_item(LabelCacheItem::default());
        let cache = BackendRepresentativeMemoryCache::default();

        assert!(cache.debug_testing_prioritized_expansion_link_duplicates(
            testing_array,
            other_label,
            &ctx
        ));
    }

    fn neighbour_linker_chain(
        ctx: &mut CacheContext,
        neighbour_ids: &[Cint64],
    ) -> Vec<IndividualRoleSetNeighbourIndividualIdLinkerId> {
        neighbour_ids
            .iter()
            .map(|id| {
                let mut linker = IndividualRoleSetNeighbourIndividualIdLinker::new();
                linker.init_individual_id_linker(*id);
                ctx.alloc_individual_role_set_neighbour_id_linker(linker)
            })
            .collect()
    }

    #[test]
    fn backend_copy_neighbour_individual_id_linkers_preserves_order_and_payloads() {
        let mut ctx = CacheContext::new();
        let source = neighbour_linker_chain(&mut ctx, &[4, 5, 6]);
        let mut cache = BackendRepresentativeMemoryCache::default();

        let copied = cache.copy_neighbour_individual_id_linkers(
            &source,
            0,
            IndividualAssociationDataId::NONE,
            -1,
            &mut ctx,
        );

        assert_eq!(copied.len(), 3);
        assert_ne!(copied, source);
        let copied_ids: Vec<_> = copied
            .iter()
            .map(|id| {
                ctx.individual_role_set_neighbour_id_linker(*id)
                    .get_individual_id()
            })
            .collect();
        assert_eq!(copied_ids, vec![4, 5, 6]);
        assert_eq!(
            cache
                .stat_individual_association_separate_memory_managment_neighbour_link_copying_count,
            3
        );
    }

    #[test]
    fn backend_copy_neighbour_individual_id_linkers_accepts_empty_chain() {
        let mut ctx = CacheContext::new();
        let mut cache = BackendRepresentativeMemoryCache::default();

        let copied = cache.copy_neighbour_individual_id_linkers(
            &[],
            0,
            IndividualAssociationDataId::NONE,
            -1,
            &mut ctx,
        );

        assert!(copied.is_empty());
        assert_eq!(
            cache
                .stat_individual_association_separate_memory_managment_neighbour_link_copying_count,
            0
        );
    }
}
