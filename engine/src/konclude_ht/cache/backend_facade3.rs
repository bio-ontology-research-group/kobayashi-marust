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

use super::super::model::substrate::Cint64;
use super::backend::BackendRepresentativeMemoryCache;
use super::backend_data::{
    BackendTempWriteRecordId, IndividualAssociationDataId,
    IndividualRoleSetNeighbourArrayId, IndividualRoleSetNeighbourIndividualIdLinkerId,
    LabelCacheItemId, LabelCacheItemType, OntologyDataId,
};
use super::value::CacheValue;

impl BackendRepresentativeMemoryCache {
    // =======================================================================
    // Basic-precomputation-mode activation
    // =======================================================================

    /// Port of `CBackendRepresentativeMemoryCache::checkBasicPrecompuationModeActivation`.
    ///
    /// W6-DEFER[api]: derefs `OntologyData` accessors (`isAssociationCompleted`,
    /// `hasBasicPrecomputationModeActivation`, `getIncompletelyHandledIndividualIdCount`,
    /// `getIndividualAssociationDataDirectUpdateCount`,
    /// `getIndividualAssociationMergingCount`) through the not-yet-wired ontology-data
    /// arena. Logic to restore: if not completed, no activation yet, >0 incompletely
    /// handled, and the configured merges/updates ratio > 0, return true when
    /// `indiMergesCount / basicIndiUpdateCount > mConfBasicPrecomputationModeActivationUpdateMergesRatio`.
    pub fn check_basic_precompuation_mode_activation(&self, ontology_data: OntologyDataId) -> bool {
        // W6-DEFER[api]: facade-arena deref of OntologyData (see doc-comment).
        let _ = ontology_data;
        false
    }

    /// Port of `CBackendRepresentativeMemoryCache::activateBasicPrecompuationMode`.
    ///
    /// W6-DEFER[api]: derefs `OntologyData` (mode flags, context, the
    /// individual-id→association-data vector) and bump-allocates a copy of that
    /// vector via the ontology context's allocation manager ([memory-pool]). Logic
    /// to restore: if not already in basic-precomputation mode and not yet
    /// activated, set both flags, snapshot `getIndividualIdAssoiationDataVector()`
    /// into a freshly allocated array, install it via
    /// `setBasicPrecomputationIndividualIdAssoiationDataVector`, log, return true.
    pub fn activate_basic_precompuation_mode(&mut self, ontology_data: OntologyDataId) -> bool {
        // W6-DEFER[api]: facade-arena deref + [memory-pool] vector clone (see doc-comment).
        let _ = ontology_data;
        false
    }

    /// Port of `CBackendRepresentativeMemoryCache::indexIndividualLabelAssociations`.
    ///
    /// W6-DEFER[api]: derefs `OntologyData` (label-association indexing counters,
    /// the individual-association-data vector, per-label extension data) and, per
    /// associatable label type, schedules a `CConcurrentTaskScheduler::run` job that
    /// walks every individual and registers it in the label item's
    /// `IndividualAssociationMap` extension. [threading]: the concurrent scheduler
    /// runs single-threaded inline in the faithful first port; [memory-pool]: each
    /// job uses its own `CMemoryPoolNewAllocationIncreasingContext`. Logic to
    /// restore: count required associatable types via `requires_individual_associations`,
    /// store the indexing count, run the per-type indexing pass, then (when
    /// `conf_wait_individual_label_association_indexed`) wait for completion.
    pub fn index_individual_label_associations(&mut self, ontology_data: OntologyDataId) {
        // W6-DEFER[api]: facade-arena deref + [threading] concurrent indexing (see doc-comment).
        let _ = ontology_data;
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
        let _ = (neighbour_id, prop_cut_indi_id_list, prop_mark_label_item, ontology_data);
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
        if let Ok(mut model_file_latest) =
            std::fs::File::create("./Debugging/RepresentativeCache/individual-label-association-data.txt")
        {
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
            == LabelCacheItemType::DeterministicCombinedExistentialInstantiatedRoleSetLabel as Cint64
        {
            label_type_string =
                "DETERMINISTIC_COMBINED_EXISTENTIAL_INSTANTIATED_ROLE_SET_LABEL".to_string();
        } else if label_type
            == LabelCacheItemType::NondeterministicCombinedExistentialInstantiatedRoleSetLabel as Cint64
        {
            label_type_string =
                "NONDETERMINISTIC_COMBINED_EXISTENTIAL_INSTANTIATED_ROLE_SET_LABEL".to_string();
        } else if label_type
            == LabelCacheItemType::DeterministicCombinedNeighbourInstantiatedRoleSetLabel as Cint64
        {
            label_type_string =
                "DETERMINISTIC_COMBINED_NEIGHBOUR_INSTANTIATED_ROLE_SET_LABEL".to_string();
        } else if label_type
            == LabelCacheItemType::NondeterministicCombinedNeighbourInstantiatedRoleSetLabel as Cint64
        {
            label_type_string =
                "NONDETERMINISTIC_COMBINED_NEIGHBOUR_INSTANTIATED_ROLE_SET_LABEL".to_string();
        } else if label_type
            == LabelCacheItemType::NeighbourInstantiatedRoleSetCombinationLabel as Cint64
        {
            label_type_string = "NEIGHBOUR_INSTANTIATED_ROLE_SET_COMBINATION_LABEL".to_string();
        } else if label_type == LabelCacheItemType::DeterministicSameIndividualSetLabel as Cint64 {
            label_type_string = "DETERMINISTIC_SAME_INDIVIDUAL_SET_LABEL".to_string();
        } else if label_type == LabelCacheItemType::NondeterministicSameIndividualSetLabel as Cint64 {
            label_type_string = "NONDETERMINISTIC_SAME_INDIVIDUAL_SET_LABEL".to_string();
        } else if label_type == LabelCacheItemType::DeterministicDiffrentIndividualSetLabel as Cint64 {
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
            let ontology_id_data_string_list = self.get_representative_cache_string_for_ontology(*ontology_data);
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
    pub fn debug_check_write_max_same_merged_individuals_to_file(&self, ontology_data: OntologyDataId) {
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
    pub fn get_representative_cache_string_for_ontology(&self, ontology_data: OntologyDataId) -> Vec<String> {
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
    ///
    /// W6-DEFER[api]: NOT macro-gated — derefs `IndividualAssociationData`'s
    /// `IndividualRoleSetNeighbourArray` and, per array position, checks the
    /// individual-id-linker count equals the stored `getIndividualCount()`, returning
    /// false on mismatch. Derefs deep storage; restore on reconcile. Returns true
    /// (no mismatch detected) until the arenas are wired.
    pub fn debug_check_neighours_correctly_counted(
        &self,
        indi_ass_data: IndividualAssociationDataId,
        ontology_data: OntologyDataId,
    ) -> bool {
        // W6-DEFER[api]: facade-arena deref over the neighbour array (see doc-comment).
        let _ = (indi_ass_data, ontology_data);
        true
    }

    // =======================================================================
    // Facade utilities
    // =======================================================================

    /// Port of `CBackendRepresentativeMemoryCache::checkAssociationComplete`.
    ///
    /// W6-DEFER[api]: when the ontology has no incompletely-handled individuals (or
    /// completion is forced), is not yet marked complete, and its first incompletely-
    /// handled individuals were retrieved, it marks the ontology data association-complete,
    /// publishes it into `fixed_ontology_identifier_data_hash` (under the write lock,
    /// [threading]), logs, and optionally runs late label-association indexing +
    /// the debug cache dump. The guard derefs `OntologyData` accessors not yet wired;
    /// restore on reconcile.
    pub fn check_association_complete(&mut self, ontology_data: OntologyDataId, force_completion: bool) {
        // W6-DEFER[api]: facade-arena deref of OntologyData guard/flags (see doc-comment).
        let _ = (ontology_data, force_completion);
    }

    /// Port of `CBackendRepresentativeMemoryCache::debugTestingPrioritizedExpansionLinkDuplicates`.
    ///
    /// W6-DEFER[api]: a debug consistency probe that visits the prop-mark array index
    /// of `testingArray` and (when `KONCLUDE_CACHE_DEBUGGING_DATA_GENERATION` data is
    /// present) detects duplicate neighbour ids. Derefs the neighbour array + its index
    /// data; restore on reconcile. Always returns true in the C++.
    pub fn debug_testing_prioritized_expansion_link_duplicates(
        &self,
        testing_array: IndividualRoleSetNeighbourArrayId,
        prop_mark_label_item: LabelCacheItemId,
    ) -> bool {
        // W6-DEFER[api]: facade-arena deref of the testing array (see doc-comment).
        let _ = (testing_array, prop_mark_label_item);
        true
    }

    /// Port of `CBackendRepresentativeMemoryCache::copyNeighbourIndividualIdLinkers`.
    ///
    /// W6-DEFER[api]: deep-copies an individual-id-linker chain into the given cache
    /// context's pool ([memory-pool]), preserving order (each copy appended at the
    /// tail), bumping the separate-memory-management neighbour-link-copying stat per
    /// link, and returning the new chain head. Derefs the linker chain + allocates via
    /// the context; restore on reconcile.
    ///
    /// KONCLUDE-PORT-NOTE[memory-pool]: `CBackendRepresentativeMemoryCacheContext*` →
    /// opaque `Cint64` allocation-context handle (no typed arena id for the abstract
    /// cache context yet).
    pub fn copy_neighbour_individual_id_linkers(
        &mut self,
        indi_id_linker: IndividualRoleSetNeighbourIndividualIdLinkerId,
        context: Cint64,
        loc_association_data: IndividualAssociationDataId,
        pos: Cint64,
    ) -> IndividualRoleSetNeighbourIndividualIdLinkerId {
        // W6-DEFER[api]: facade-arena deref + [memory-pool] linker copy (see doc-comment).
        let _ = (indi_id_linker, context, loc_association_data, pos);
        IndividualRoleSetNeighbourIndividualIdLinkerId::NONE
    }
}
