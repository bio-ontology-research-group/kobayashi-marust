//! `cache::backend_facade2` — F1 facade method bodies, **MIDDLE third** of
//! `CBackendRepresentativeMemoryCache::*` (Konclude
//! `Source/Reasoner/Kernel/Cache/CBackendRepresentativeMemoryCache.cpp`).
//!
//! ## Range taken (PORT.md §W6 cache-skeleton; `// W6-CACHE method-batch`)
//!
//! The facade's `CBackendRepresentativeMemoryCache::` method-definition span runs
//! from the constructor at **cpp line 34** to the last method (~line 5322); the
//! file ends at 5351. Dividing that span into thirds by source line gives a third
//! size of ≈1772 lines, so the MIDDLE third covers method DEFINITIONS whose start
//! line falls in `[1806, 3579)`. By the start-line assignment (the giant
//! `installAssociationUpdate`, 1620–2762, starts in the first third) this file
//! ports the methods at cpp lines **2763 → 3957**:
//!
//! * `updateIndexedAssociationCount` (×2 overloads, 2763 / 2791),
//! * `udateDeterministicSameAssociations` (2829),
//! * `completeSameAsNeighbours` (2855),
//! * `completeDeterministicSameAsMergingInformation` (2938),
//! * `completeNeighboursForSameAsMerging` (3072),
//! * `storeIndividualIncompletelyMarked` (3176),
//! * `installNominalIndirectConncetionUpdates` (3223),
//! * `setUpdatedIndividualAssociationData` (3291),
//! * `getIncompletlyAssociationCachedIndividuals` (3321),
//! * `initializeIndividualsAssociationCaching` (3346),
//! * `reportMaximumHandledRecomputationId` (3358),
//! * `requiresIndividualAssociations` (3370),
//! * `getIndividualAssociationsExtensionData` (3380),
//! * `getIndividualNeighbourArrayIndexExtensionData` (3391),
//! * `getNeighbourArrayRoleTagResolvingLabelExtensionData` (3403),
//! * `getMinimumSlotReferreringInstalledValidRecomputationId` (3435),
//! * `processCustomsEvents` (3484–3957, the cross-thread event dispatcher).
//!
//! ## Port status (struct-def era — no cache arena yet)
//!
//! Same situation as the W3 pre-3.5 wave: the F1 per-ontology / per-individual /
//! label arenas (`Arena<OntologyData>` / `Arena<IndividualAssociationData>` /
//! `Arena<LabelCacheItem>` …) and the cache context that owns them are NOT yet
//! ported, so an `OntologyDataId` / `IndividualAssociationDataId` /
//! `LabelCacheItemId` cannot be resolved to an object. Every such dereference is a
//! `// W6-DEFER[api]` (the precedent set by `value::CacheValueHasher::get_hash_value`).
//! Reachable FACADE-field reads/writes (`self.next_indi_update_id`,
//! `self.stat_*`, the conf flags, the tmp sets) and **sibling facade calls**
//! (`self.x(...)` — siblings defined in the first/last-third facade files, resolved
//! at the assembly wave) are ported live; only the arena-bound inner logic is
//! deferred, with the faithful C++ control flow preserved in the deferred block.
//! No logic is dropped.
//!
//! ## License (per `PORT.md` §License note)
//! Function-by-function translation of LGPLv3 Konclude source.
//!
//! ## Port conventions (PORT.md §44) — same as `backend.rs`
//! * `CXxx*` → typed arena `Id<T>` (`Id::NONE` == null);
//! * `QSet<cint64>` / `QHash<cint64,cint64>` params → `HashSet`/`HashMap`;
//! * `QMutex`/`QSemaphore`/`QEvent` → `[threading]` single-thread inline;
//! * cross-family / infra pointers (`CCallbackData*`, the coordination hashes) →
//!   opaque `Cint64` `[api]`.

#![allow(dead_code, unused_variables, unused_mut)]

use std::collections::{HashMap, HashSet};

use super::super::model::substrate::{Cint64, Id};
use super::backend::BackendRepresentativeMemoryCache;
use super::backend_data::{
    BackendTempWriteRecordId, IndividualAssociationDataId, LabelCacheItemExtensionDataId,
    LabelCacheItemId, LabelCacheItemType, OntologyDataId,
};
use super::value;

impl BackendRepresentativeMemoryCache {
    /// Port of `CBackendRepresentativeMemoryCache::updateIndexedAssociationCount`
    /// (the `(locAssociationData, prevLabelItem, i, ontologyData)` overload, cpp 2763).
    ///
    /// Adjusts the per-label individual-association counters when the label entry
    /// at index `i` changed from `prevLabelItem` to the new entry: dec the previous
    /// item's count (and remove its id from the association map when exact tracking
    /// is required and late indexing is off), inc the new item's count (and add).
    pub fn update_indexed_association_count(
        &mut self,
        loc_association_data: IndividualAssociationDataId,
        prev_label_item: LabelCacheItemId,
        i: Cint64,
        ontology_data: OntologyDataId,
    ) -> bool {
        let mut updated = false;
        let exact_indi_assoc_tracking = self.requires_individual_associations(i);

        // W6-DEFER[api]: newLabelItem = ctx.assoc(loc_association_data).get_label_cache_entry(i);
        //   if prevLabelItem != newLabelItem {
        //     if prevLabelItem {
        //       updated = true; ctx.label(prevLabelItem).dec_individual_association_count();
        //       if exactIndiAssocTracking && !mConfLateIndividualLabelAssociationIndexing {
        //         indiAssoExtData = self.get_individual_associations_extension_data(prevLabelItem, ontologyData);
        //         indiAssoExtData.remove_individual_id_association(loc_association_data);
        //       }
        //     }
        //     if newLabelItem {
        //       updated = true; ctx.label(newLabelItem).inc_individual_association_count();
        //       if exactIndiAssocTracking && !mConfLateIndividualLabelAssociationIndexing {
        //         indiAssoExtData = self.get_individual_associations_extension_data(newLabelItem, ontologyData);
        //         indiAssoExtData.add_individual_id_association(loc_association_data);
        //       }
        //     }
        //   }
        let _ = (loc_association_data, prev_label_item, ontology_data, exact_indi_assoc_tracking);
        let _ = &mut updated;
        true
    }

    /// Port of `CBackendRepresentativeMemoryCache::updateIndexedAssociationCount`
    /// (the `(locAssociationData, associationData, i, ontologyData)` overload, cpp 2791).
    ///
    /// KONCLUDE-PORT-NOTE[overload]: Rust cannot overload by argument type; this is
    /// the variant whose second argument is the previous *association data* (not a
    /// label item). It additionally re-counts when the representative-same-as
    /// merging changed (`sameIndiMergedChanged`).
    pub fn update_indexed_association_count_for_association_data(
        &mut self,
        loc_association_data: IndividualAssociationDataId,
        association_data: IndividualAssociationDataId,
        i: Cint64,
        ontology_data: OntologyDataId,
    ) -> bool {
        let mut updated = false;
        let exact_indi_assoc_tracking = self.requires_individual_associations(i);

        // W6-DEFER[api]: faithful body:
        //   sameIndiMergedChanged = !associationData
        //       || ctx.assoc(associationData).get_representative_same_individual_id()
        //          != ctx.assoc(loc_association_data).get_representative_same_individual_id();
        //   prevLabelItem = associationData ? ctx.assoc(associationData).get_label_cache_entry(i) : NONE;
        //   newLabelItem  = ctx.assoc(loc_association_data).get_label_cache_entry(i);
        //   if prevLabelItem != newLabelItem || sameIndiMergedChanged {
        //     if prevLabelItem { updated; ctx.label(prevLabelItem).dec_individual_association_count();
        //       if exact && !mConfLate { self.get_individual_associations_extension_data(prevLabelItem, ontologyData)
        //         .remove_individual_id_association(associationData); } }
        //     if newLabelItem { updated; ctx.label(newLabelItem).inc_individual_association_count();
        //       if exact && !mConfLate { self.get_individual_associations_extension_data(newLabelItem, ontologyData)
        //         .add_individual_id_association(loc_association_data); } }
        //   }
        let _ = (loc_association_data, association_data, ontology_data, exact_indi_assoc_tracking);
        let _ = &mut updated;
        true
    }

    /// Port of `CBackendRepresentativeMemoryCache::udateDeterministicSameAssociations`
    /// (cpp 2829; the original C++ name typo "udate" is preserved as an anchor).
    ///
    /// Walks the deterministic-merged same-individual label of `locNeighbourAssociationData`
    /// and, for every other neighbour that points its deterministic-same id back at
    /// this individual, (re)installs the deterministic-same-as association update.
    pub fn udate_deterministic_same_associations(
        &mut self,
        loc_neighbour_association_data: IndividualAssociationDataId,
        ontology_data: OntologyDataId,
    ) -> bool {
        let mut updated = false;

        // W6-DEFER[api]: faithful body:
        //   detSameLabItem = ctx.assoc(locNeighbourAssociationData)
        //       .get_deterministic_merged_same_considered_label_cache_entry();
        //   if detSameLabItem {
        //     for detSameValueLinker in ctx.label(detSameLabItem).cache_value_linkers() {
        //       detSameNeighbourId = detSameValueLinker.get_cache_value().get_tag();
        //       if detSameNeighbourId != ctx.assoc(loc...).get_associated_individual_id() {
        //         detSameNeighbourAssociationData = (ontologyData has vector && id in range)
        //             ? ctx.ontology(ontologyData).indi_id_asso_data_vector()[detSameNeighbourId] : NONE;
        //         if detSameNeighbourAssociationData
        //            && ctx.assoc(detSameNeighbourAssociationData).get_deterministic_same_individual_id()
        //               == ctx.assoc(loc...).get_associated_individual_id() {
        //           if self.check_requires_deterministic_same_as_association_update_installation(
        //                   detSameNeighbourAssociationData, detSameNeighbourId,
        //                   loc_neighbour_association_data, locAssocId, ontologyData) {
        //             updated |= self.install_deterministic_same_as_association_update(
        //                   detSameNeighbourAssociationData, detSameNeighbourId,
        //                   loc_neighbour_association_data, locAssocId, ontologyData);
        //           }
        //         }
        //       }
        //     }
        //   }
        let _ = (loc_neighbour_association_data, ontology_data);
        let _ = &mut updated;
        updated
    }

    /// Port of `CBackendRepresentativeMemoryCache::completeSameAsNeighbours` (cpp 2855).
    ///
    /// For each newly-completing deterministic-same neighbour, copies the missing
    /// neighbour-role-set links from that neighbour's role-set array into this
    /// individual's neighbour hash/array (allocating new neighbour-id linkers),
    /// rejecting incompatible role-set labels when `completeOnlyCompatibleNeighbourRoleLabels`.
    /// Touches the neighbour-completion statistics on the facade.
    pub fn complete_same_as_neighbours(
        &mut self,
        loc_association_data: IndividualAssociationDataId,
        new_completing_det_same_neighbours: HashSet<Cint64>,
        newly_completed_det_same_neighbours: &mut HashSet<Cint64>,
        complete_only_compatible_neighbour_role_labels: bool,
        ontology_data: OntologyDataId,
    ) -> bool {
        let mut completed = false;
        let mut links_completed: Cint64 = 0;

        // W6-DEFER[api]: faithful body (≈75 lines):
        //   context = ctx.ontology(ontologyData).get_ontology_context();
        //   detSameLabItem = ctx.assoc(loc...).get_label_cache_entry(DETERMINISTIC_SAME_INDIVIDUAL_SET_LABEL);
        //   neighbourRoleSetLabelItemHash = ctx.assoc(loc...).get_neighbour_role_set_hash();
        //   neighbourArray = ctx.assoc(loc...).get_role_set_neighbour_array();
        //   arrayIndexData = neighbourArray.get_index_data();
        //   if detSameLabItem {
        //     for detSameValueLinker in detSameLabItem.cache_value_linkers() {
        //       detSameId = detSameValueLinker.cache_value().get_tag();
        //       if detSameId != locAssocId && new_completing_det_same_neighbours.contains(detSameId) {
        //         detSameAssociationData = ctx.ontology(ontologyData).indi_id_asso_data_vector()[detSameId];
        //         if !detSameAssociationData.has_deterministic_same_individual_merging() {
        //           completedDetSameId = true; oneChanged = false; oneIncompatible = false;
        //           detSameNeighbourArray = detSameAssociationData.get_role_set_neighbour_array();
        //           if detSameNeighbourArray {
        //             detSameArrayIndexData = detSameNeighbourArray.get_index_data();
        //             for i in 0..detSameArrayIndexData.get_array_size() while completedDetSameId {
        //               detSameNeighbourRoleSetLabelItem = detSameArrayIndexData.get_neighbour_role_set_label(i);
        //               arrayIndex = arrayIndexData.get_index(detSameNeighbourRoleSetLabelItem);
        //               if arrayIndex >= 0 {
        //                 neighbourData = neighbourArray.at(arrayIndex);
        //                 for neighbourIndiLinker in detSameNeighbourArray.at(i).individual_id_linkers() while completedDetSameId {
        //                   neighbourIndiId = neighbourIndiLinker.get_individual_id();
        //                   neighbourRoleSetLabelItem = neighbourRoleSetLabelItemHash.get_neighbour_role_set_label(neighbourIndiId);
        //                   if !neighbourRoleSetLabelItem {
        //                     neighbourRoleSetLabelItemHash.set_neighbour_role_set_label(neighbourIndiId, detSameNeighbourRoleSetLabelItem);
        //                     newLinker = ctx.alloc_neighbour_id_linker(neighbourIndiId);
        //                     self.stat_created_neighbour_links += 1; links_completed += 1;
        //                     neighbourData.add_individual_id_linker(newLinker, true);
        //                   } else if neighbourRoleSetLabelItem != detSameNeighbourRoleSetLabelItem {
        //                     oneChanged = true; self.stat_changed_label_neighbour_completion_count += 1;
        //                     if complete_only_compatible_neighbour_role_labels {
        //                       completedDetSameId = false;
        //                       self.stat_incompatible_label_neighbour_completion_count += 1; oneIncompatible = true;
        //                     }
        //                   }
        //                 }
        //               }
        //             }
        //           }
        //           if completedDetSameId { newly_completed_det_same_neighbours.insert(detSameId);
        //             completed = true; self.stat_neighbour_completion_det_same_succeded_count += 1; }
        //           if oneChanged { self.stat_neighbour_completion_det_same_changed_count += 1; }
        //           if oneIncompatible { self.stat_neighbour_completion_det_same_incompatible_count += 1; }
        //           if !oneChanged { self.stat_neighbour_completion_det_same_unchanged_count += 1; }
        //         } else { newly_completed_det_same_neighbours.insert(detSameId); }
        //       }
        //     }
        //   }
        let _ = (
            loc_association_data,
            new_completing_det_same_neighbours,
            &mut *newly_completed_det_same_neighbours,
            complete_only_compatible_neighbour_role_labels,
            ontology_data,
        );
        let _ = (&mut completed, &mut links_completed);
        completed
    }

    /// Port of `CBackendRepresentativeMemoryCache::completeDeterministicSameAsMergingInformation`
    /// (cpp 2938).
    ///
    /// For every destination of the completion-reference hash, transitively merges
    /// all reachable deterministic-same labels (a worklist closure over the
    /// `DETERMINISTIC_SAME_INDIVIDUAL_SET_LABEL` linkers), folds them into one merged
    /// label via `getAdditionMergedLabel`, then re-localises every member individual
    /// to that merged label, the minimum representative id, and completely/incompletely
    /// -handled state, restoring the per-individual association data.
    pub fn complete_deterministic_same_as_merging_information(
        &mut self,
        tmp_det_same_merging_completion_reference_hash: &mut HashMap<Cint64, Cint64>,
        ontology_data: OntologyDataId,
    ) -> bool {
        let mut updated = false;
        let mut completed_det_same_label_items: Cint64 = 0;
        let mut completed_det_same_integrated_individuals: Cint64 = 0;
        let mut completed_individual_updates: Cint64 = 0;

        // W6-DEFER[api]: faithful body (≈125 lines). Outline (sibling calls live on
        // reconcile; facade-field mutations shown inline below the arena resolves):
        //   mergedHandledIndiIdSet: HashSet<cint64>;
        //   for (refIndiId, destIndiId) in tmp_det_same_merging_completion_reference_hash {
        //     if !mergedHandledIndiIdSet.contains(destIndiId) {
        //       mergedHandledIndiIdSet.insert(destIndiId); completed_det_same_label_items += 1;
        //       refIndiAssociationData = ctx.ontology(ontologyData).indi_id_asso_data_vector()[destIndiId];
        //       detSameLabItem = ctx.assoc(refIndiAssociationData).get_label_cache_entry(DET_SAME_INDIVIDUAL_SET_LABEL);
        //       if detSameLabItem {
        //         // worklist closure over merging det-same label items, tracking minRepIndiId;
        //         // each visited detSameId: mergedHandledIndiIdSet.insert(detSameId);
        //         //   minRepIndiId = min(detSameId, minRepIndiId); completed_det_same_integrated_individuals += 1;
        //         //   enqueue other/dest det-same label items not yet in the merging set;
        //         mergedDetSameLabItem = detSameLabItem;
        //         for mergingLabelItem in mergingDetSameLabelItemSet if mergingLabelItem != detSameLabItem:
        //           mergedDetSameLabItem = self.get_addition_merged_label(
        //               DET_SAME_INDIVIDUAL_SET_LABEL, mergingLabelItem, mergedDetSameLabItem, ontologyData);
        //         for detSameValueLinker in mergedDetSameLabItem.cache_value_linkers() {
        //           detSameId = ...; sameIndiAssociationData = vector[detSameId];
        //           if (label != mergedDetSameLabItem || repSameId != minRepIndiId
        //               || (assocId == minRepIndiId && isCompletelyHandled)) {
        //             incrementUpdateId = self.conf_increment_update_id_for_deterministic_same_as_completion;
        //             if assocId == minRepIndiId { incrementUpdateId = true; }
        //             locSameIndiAssociationData = self.create_localized_individual_association_data(
        //                 assocId, sameIndiAssociationData, ontologyData, false, incrementUpdateId);
        //             context = self.get_individual_association_data_memory_context(locSameIndiAssociationData, ontologyData);
        //             locSame.set_cache_update_id(self.next_indi_update_id); self.next_indi_update_id += 1;
        //             locSame.set_neighbour_role_set_hash(sameIndi.get_neighbour_role_set_hash());
        //             locSame.set_role_set_neighbour_array(sameIndi.get_role_set_neighbour_array());
        //             locSame.set_representative_same_individual_id(minRepIndiId);
        //             if locSame.has_representative_same_individual_merging()
        //                && (!sameIndi || !sameIndi.has_representative_same_individual_merging()) {
        //               self.stat_det_same_representative_merging_count += 1;
        //               ctx.ontology(ontologyData).inc_individual_association_merging_count();
        //             }
        //             locSame.set_label_cache_entry(DET_SAME_INDIVIDUAL_SET_LABEL, mergedDetSameLabItem);
        //             self.update_indexed_association_count_for_association_data(
        //                 locSameIndiAssociationData, sameIndiAssociationData, DET_SAME_INDIVIDUAL_SET_LABEL, ontologyData);
        //             locSame.set_completely_handled(detSameId != minRepIndiId);
        //             self.updated_indi_count += 1; completed_individual_updates += 1;
        //             ctx.ontology(ontologyData).set_max_individual_association_data_update_count(
        //                 max(locSame.get_association_data_update_id(), ontology.get_max_individual_association_data_update_count()));
        //             self.store_individual_incompletely_marked(
        //                 locSameIndiAssociationData, !locSame.is_completely_handled(), ontologyData);
        //             self.set_updated_individual_association_data(assocId, locSameIndiAssociationData, ontologyData);
        //             updated = true;
        //           }
        //         }
        //       }
        //     }
        //   }
        //   LOG(...completed_det_same_label_items / _integrated_individuals / _individual_updates...);
        let _ = (
            &mut *tmp_det_same_merging_completion_reference_hash,
            ontology_data,
            self.conf_increment_update_id_for_deterministic_same_as_completion,
            self.current_update_handling_recomputation_id,
        );
        let _ = (
            &mut updated,
            &mut completed_det_same_label_items,
            &mut completed_det_same_integrated_individuals,
            &mut completed_individual_updates,
        );
        updated
    }

    /// Port of `CBackendRepresentativeMemoryCache::completeNeighboursForSameAsMerging`
    /// (cpp 3072).
    ///
    /// For each merged individual in `mTmpCompleteNeighbourSameIndiMergingSet`, for
    /// every neighbour that is not deterministically-same-merged, finds the shared
    /// role-set label among the det-same ids and copies the missing det-same
    /// neighbour links into a freshly localised neighbour-association data (new array
    /// + hash), then stores + re-derives the deterministic-same associations.
    pub fn complete_neighbours_for_same_as_merging(
        &mut self,
        tmp_complete_neighbour_same_indi_merging_set: &mut HashSet<Cint64>,
        ontology_data: OntologyDataId,
    ) -> bool {
        let mut updated = false;
        let mut checking_neighbours: Cint64 = 0;
        let mut completed_neighbours: Cint64 = 0;
        let mut completed_neighbour_links: Cint64 = 0;

        // KONCLUDE-PORT-NOTE[api]: the C++ iterates the FACADE field
        // `mTmpCompleteNeighbourSameIndiMergingSet` (self.tmp_complete_neighbour_same_indi_merging_set),
        // not the by-value `tmp_complete_neighbour_same_indi_merging_set` param — the
        // param is the same set passed by the caller. Faithful iteration uses the field.
        //
        // W6-DEFER[api]: faithful body (≈100 lines):
        //   context = ctx.ontology(ontologyData).get_ontology_context();
        //   tmpLocalIndiAssocDataHash: HashMap<cint64, IndividualAssociationDataId>;
        //   for mergeIndiId in self.tmp_complete_neighbour_same_indi_merging_set {
        //     associationData = vector[mergeIndiId];
        //     detSameLabItem = associationData.get_label_cache_entry(DET_SAME_INDIVIDUAL_SET_LABEL);
        //     if detSameLabItem {
        //       neighbourArray = associationData.get_role_set_neighbour_array();
        //       arrayIndexData = neighbourArray.get_index_data();
        //       for i in 0..arrayIndexData.get_array_size() {
        //         for neighbourIndiLinker in neighbourArray.at(i).individual_id_linkers() {
        //           neighbourIndiId = ...; checking_neighbours += 1;
        //           neighbourAssociationData = vector[neighbourIndiId];
        //           if !neighbourAssociationData.has_deterministic_same_individual_merging() {
        //             // find the shared role-set label + array id over the det-same ids;
        //             // for each missing det-same id:
        //             //   lazily create localized neighbour assoc data into tmpLocalIndiAssocDataHash:
        //             //     createLocalizedIndividualAssociationData(...);
        //             //     getIndividualAssociationDataMemoryContext(..., &requiresDataCopying);
        //             //     newArray/newNeighbourRoleSetHash alloc + init (copy);
        //             //     setNeighbourRoleSetHash/setRoleSetNeighbourArray;
        //             //     set_cache_update_id(self.next_indi_update_id); self.next_indi_update_id += 1;
        //             //     set_max_individual_association_data_update_count(...);
        //             //     self.updated_indi_count += 1; completed_neighbours += 1;
        //             //   newLinker = ctx.alloc_neighbour_id_linker(detSameId);
        //             //   self.stat_created_neighbour_links += 1;
        //             //   locArray.at(sameArrayId).add_individual_id_linker(newLinker);
        //             //   locHash.set_neighbour_role_set_label(detSameId, sameNeighbourRoleSetLabelItem);
        //             //   completed_neighbour_links += 1;
        //           }
        //         }
        //       }
        //     }
        //   }
        //   for (_, locNeighbourAssociationData) in tmpLocalIndiAssocDataHash {
        //     self.store_individual_incompletely_marked(locNeighbourAssociationData,
        //         !ctx.assoc(loc...).is_completely_handled(), ontologyData);
        //     self.set_updated_individual_association_data(loc...assocId, locNeighbourAssociationData, ontologyData);
        //     updated |= self.udate_deterministic_same_associations(locNeighbourAssociationData, ontologyData);
        //   }
        //   LOG(...completed_neighbour_links / completed_neighbours / set.size() / checking_neighbours...);
        let _ = (&mut *tmp_complete_neighbour_same_indi_merging_set, ontology_data);
        let _ = (
            &mut updated,
            &mut checking_neighbours,
            &mut completed_neighbours,
            &mut completed_neighbour_links,
        );
        updated
    }

    /// Port of `CBackendRepresentativeMemoryCache::storeIndividualIncompletelyMarked`
    /// (cpp 3176).
    ///
    /// Flips an individual's incompletely-marked flag and keeps the ontology data's
    /// incompletely-handled count and the problematic-incompletely-handled set in
    /// sync (allocating the set lazily when a problematic-level individual is first
    /// marked).
    pub fn store_individual_incompletely_marked(
        &mut self,
        loc_association_data: IndividualAssociationDataId,
        mark_incompletely_handled: bool,
        ontology_data: OntologyDataId,
    ) -> bool {
        let mut associations_updated = false;

        // W6-DEFER[api]: faithful body:
        //   individualID = ctx.assoc(loc_association_data).get_associated_individual_id();
        //   if !mark_incompletely_handled {
        //     if ctx.assoc(loc...).is_incompletely_marked() {
        //       ctx.ontology(ontologyData).dec_incompletely_handled_individual_id_count();
        //       ctx.assoc(loc...).set_incompletely_marked(false); associations_updated = true;
        //       if ctx.assoc(loc...).has_problematic_level() {
        //         if propIndiSet = ctx.ontology(ontologyData).get_problematic_incompletely_handled_individual_set() {
        //           propIndiSet.remove(individualID);
        //         }
        //       }
        //     }
        //   } else {
        //     ctx.ontology(ontologyData).set_last_min_incompletely_handled_indi_id(
        //         min(ontology.get_last_min_incompletely_handled_indi_id(), individualID));
        //     if !ctx.assoc(loc...).is_incompletely_marked() {
        //       ctx.ontology(ontologyData).inc_incompletely_handled_individual_id_count();
        //       ctx.assoc(loc...).set_incompletely_marked(true); associations_updated = true;
        //       if ctx.assoc(loc...).has_problematic_level() {
        //         propIndiSet = ctx.ontology(ontologyData).get_problematic_incompletely_handled_individual_set();
        //         if !propIndiSet { propIndiSet = ctx.alloc_problematic_set(ontology.get_ontology_context()); }
        //         propIndiSet.insert(individualID);
        //       }
        //     }
        //   }
        let _ = (loc_association_data, mark_incompletely_handled, ontology_data);
        let _ = &mut associations_updated;
        associations_updated
    }

    /// Port of `CBackendRepresentativeMemoryCache::installNominalIndirectConncetionUpdates`
    /// (cpp 3223; the C++ name typo "Conncetion" is preserved as an anchor).
    ///
    /// Walks the temporary nominal-indirect-connection write chain: for each nominal,
    /// (re)marks the referenced individual association incompletely handled when the
    /// integration id moved, installs a fresh nominal-indirect-connection data node,
    /// and appends every not-already-present indirectly-connected individual id
    /// (de-duplicating against the cached / temporary indirectly-connected-nominal label).
    pub fn install_nominal_indirect_conncetion_updates(
        &mut self,
        temp_nom_indirect_conn_data_linker: BackendTempWriteRecordId,
        ontology_data: OntologyDataId,
    ) -> bool {
        let mut connection_data_updated = false;

        // W6-DEFER[api]: faithful body (≈60 lines):
        //   context = ctx.ontology(ontologyData).get_ontology_context();
        //   for tempNomIndirectConnDataLinkerIt in chain(temp_nom_indirect_conn_data_linker) {
        //     nomIndiId = it.individual_id; indirectlyConnectedIds = it.indirectly_connected_individual_id_linker;
        //     lastChangeIntegrationId = it.last_integration_id;
        //     nomConnData& = ctx.ontology(ontologyData).nominal_indi_id_indirect_connection_data_hash[nomIndiId];
        //     prevNomConnData = nomConnData;
        //     nominalAssociationData = (vector has nomIndiId) ? vector[nomIndiId] : NONE;
        //     if (nominalAssociationData && nominal.get_last_integrated_..._change_id() != lastChangeIntegrationId && last>0)
        //        || (nominalAssociationData && prevNomConnData && last==0 && nominal.has_indirectly_connected_individual_integration()
        //            && prevNomConnData.get_last_change_id() != nominal.get_last_integrated_..._change_id()) {
        //       connection_data_updated |= self.mark_representative_referenced_individual_association_incompletely_handled(
        //           nomIndiId, nominalAssociationData, ontologyData);
        //     }
        //     newNomConnData = ctx.alloc_nominal_indirect_connection_data();
        //     newNomConnData.init_nominal_individual_indirect_connection_data(prevNomConnData);
        //     nomConnData = newNomConnData;
        //     newNomConnData.set_last_change_id(self.next_nom_conn_update_id); self.next_nom_conn_update_id += 1;
        //     for indiId in indirectlyConnectedIds {
        //       associationData = (vector has indiId) ? vector[indiId] : NONE;
        //       indiConnNomIndiIdSetLabel =
        //          (associationData && assoc.get_cache_update_id() < self.tmp_indi_assoc_prev_update_id)
        //            ? assoc.get_label_cache_entry(INDIRECTLY_CONNECTED_NOMINAL_INDIVIDUAL_SET_LABEL)
        //            : self.tmp_indi_indirectly_conn_nom_label_item_hash.get(indiId);
        //       alreadyPresent = indiConnNomIndiIdSetLabel && label.has_cached_tag_value(nomIndiId);
        //       if !alreadyPresent {
        //         indiLinker = ctx.alloc_xlinker(indiId);
        //         newNomConnData.add_indirectly_connected_individual_id_linker(indiLinker);
        //         connection_data_updated = true;
        //       }
        //     }
        //   }
        let _ = (
            temp_nom_indirect_conn_data_linker,
            ontology_data,
            self.tmp_indi_assoc_prev_update_id,
        );
        let _ = &mut connection_data_updated;
        connection_data_updated
    }

    /// Port of `CBackendRepresentativeMemoryCache::setUpdatedIndividualAssociationData`
    /// (cpp 3291).
    ///
    /// Stores the localised association data into the ontology's indi-id → data
    /// vector (growing the vector by ×10 when the id is out of range, copying old
    /// entries), updating the max-stored-id, the associations count, and the
    /// association-data update count.
    pub fn set_updated_individual_association_data(
        &mut self,
        individual_id: Cint64,
        loc_association_data: IndividualAssociationDataId,
        ontology_data: OntologyDataId,
    ) {
        // W6-DEFER[api]: faithful body:
        //   context = ctx.ontology(ontologyData).get_ontology_context();
        //   indiIdAssoDataVector = ctx.ontology(ontologyData).indi_id_asso_data_vector();
        //   indiIdAssoDataVectorSize = ctx.ontology(ontologyData).get_indi_id_asso_data_vector_size();
        //   if individual_id >= indiIdAssoDataVectorSize {
        //     prevSize = indiIdAssoDataVectorSize;
        //     indiIdAssoDataVectorSize = max(indiIdAssoDataVectorSize * 10, individual_id);
        //     newVector = ctx.alloc_assoc_data_vector(indiIdAssoDataVectorSize) (NONE-filled);
        //     copy [0..prevSize); set_indi_id_asso_data_vector(size, newVector);
        //   }
        //   ctx.ontology(ontologyData).update_max_stored_indvidual_id(individual_id);
        //   if !indiIdAssoDataVector[individual_id] { ctx.ontology(ontologyData).inc_individual_associations_count(); }
        //   if ctx.assoc(loc...).get_previous_data() && !ctx.assoc(loc...).get_previous_data().get_previous_data() {
        //     ctx.ontology(ontologyData).inc_individual_association_data_update_count();
        //   }
        //   indiIdAssoDataVector[individual_id] = loc_association_data;
        let _ = (individual_id, loc_association_data, ontology_data);
    }

    /// Port of `CBackendRepresentativeMemoryCache::getIncompletlyAssociationCachedIndividuals`
    /// (cpp 3321).
    ///
    /// Public API: queues (or, in direct-update-sync mode, runs inline) a
    /// `CRetrieveIncompletelyAssociationCachedEvent`, blocking on a callback when the
    /// caller passes none.
    ///
    /// KONCLUDE-PORT-NOTE[api]: the coordination-hash pointers + `CCallbackData*` are
    /// caller-owned infra → opaque `Cint64`. KONCLUDE-PORT-NOTE[threading]: the
    /// `QMutex` direct-sync lock and the `CBlockingCallbackData::waitForCallback`
    /// are dropped in the single-thread staging (worker == writer); the direct path
    /// runs `process_customs_events` inline.
    pub fn get_incompletly_association_cached_individuals(
        &mut self,
        ontology_identifier: Cint64,
        prev_coord_hash: Cint64,
        new_coord_hash: Cint64,
        all_individuals_added: bool,
        refill_retrieval_coord_hash: bool,
        limit: Cint64,
        callback_data: Cint64,
    ) -> bool {
        if callback_data == super::super::model::substrate::INVALID {
            // C++: `if (!callbackData)` — null callback ⇒ build a blocking callback
            // (the opaque `CCallbackData*` null is the `INVALID` sentinel).
            // [threading] W6-DEFER[api]: CBlockingCallbackData blockingCallbackData;
            if self.conf_direct_update_synchronization {
                // [threading]: mDirectUpdateSyncMutex.lock() dropped (single-thread).
                // W6-DEFER[api]: procEvent = new CRetrieveIncompletelyAssociationCachedEvent(
                //     &blockingCallbackData, ontology_identifier, prev_coord_hash, new_coord_hash,
                //     all_individuals_added, refill_retrieval_coord_hash, limit);
                self.process_customs_events(
                    value::event::RETRIEVE_INCOMPLETELY_ASSOCIATION_CACHED,
                    super::super::model::substrate::INVALID,
                );
                // [threading]: mDirectUpdateSyncMutex.unlock() dropped.
            } else {
                // [threading] W6-DEFER[api]: postEvent(new CRetrieveIncompletelyAssociationCachedEvent(...));
            }
            // [threading]: blockingCallbackData.waitForCallback() dropped (inline above).
        } else {
            if self.conf_direct_update_synchronization {
                // [threading]: lock dropped.
                // W6-DEFER[api]: procEvent = new CRetrieveIncompletelyAssociationCachedEvent(callbackData, ...);
                self.process_customs_events(
                    value::event::RETRIEVE_INCOMPLETELY_ASSOCIATION_CACHED,
                    super::super::model::substrate::INVALID,
                );
                // [threading]: unlock dropped.
            } else {
                // [threading] W6-DEFER[api]: postEvent(new CRetrieveIncompletelyAssociationCachedEvent(callbackData, ...));
            }
        }
        let _ = (
            ontology_identifier,
            prev_coord_hash,
            new_coord_hash,
            all_individuals_added,
            refill_retrieval_coord_hash,
            limit,
        );
        true
    }

    /// Port of `CBackendRepresentativeMemoryCache::initializeIndividualsAssociationCaching`
    /// (cpp 3346). Queues / inline-runs a `CInitializeIndividualAssociationsCacheEvent`.
    /// KONCLUDE-PORT-NOTE[threading]: the direct-sync `QMutex` is dropped (single-thread).
    pub fn initialize_individuals_association_caching(
        &mut self,
        ontology_identifier: Cint64,
        individual_count: Cint64,
    ) -> bool {
        if self.conf_direct_update_synchronization {
            // [threading]: mDirectUpdateSyncMutex.lock()/unlock() dropped.
            // W6-DEFER[api]: procEvent = new CInitializeIndividualAssociationsCacheEvent(
            //     ontology_identifier, individual_count);
            self.process_customs_events(
                value::event::INITIALIZE_INDIVIDUALS_ASSOCIATIONS_CACHE,
                super::super::model::substrate::INVALID,
            );
        } else {
            // [threading] W6-DEFER[api]: postEvent(new CInitializeIndividualAssociationsCacheEvent(...));
        }
        let _ = (ontology_identifier, individual_count);
        true
    }

    /// Port of `CBackendRepresentativeMemoryCache::reportMaximumHandledRecomputationId`
    /// (cpp 3358). Queues / inline-runs a `CReportMaximumHandledRecomputationIdsEvent`.
    /// KONCLUDE-PORT-NOTE[threading]: the direct-sync `QMutex` is dropped (single-thread).
    pub fn report_maximum_handled_recomputation_id(
        &mut self,
        ontology_identifier: Cint64,
        maximum_recomputation_id: Cint64,
    ) -> bool {
        if self.conf_direct_update_synchronization {
            // [threading]: lock/unlock dropped.
            // W6-DEFER[api]: procEvent = new CReportMaximumHandledRecomputationIdsEvent(
            //     ontology_identifier, maximum_recomputation_id);
            self.process_customs_events(
                value::event::REPORT_MAXIMUM_HANDLED_RECOMPUTATION_ID,
                super::super::model::substrate::INVALID,
            );
        } else {
            // [threading] W6-DEFER[api]: postEvent(new CReportMaximumHandledRecomputationIdsEvent(...));
        }
        let _ = (ontology_identifier, maximum_recomputation_id);
        true
    }

    /// Port of `CBackendRepresentativeMemoryCache::requiresIndividualAssociations`
    /// (cpp 3370).
    ///
    /// Pure predicate over the label type: the full-concept / neighbour-combination /
    /// existential-role / same-individual / data-role label kinds require exact
    /// individual-association tracking. Fully ported (no arena dereference).
    pub fn requires_individual_associations(&self, label_type: Cint64) -> bool {
        if label_type == LabelCacheItemType::FullConceptSetLabel as Cint64
            || label_type == LabelCacheItemType::NeighbourInstantiatedRoleSetCombinationLabel as Cint64
            || label_type
                == LabelCacheItemType::DeterministicCombinedExistentialInstantiatedRoleSetLabel as Cint64
            || label_type
                == LabelCacheItemType::NondeterministicCombinedExistentialInstantiatedRoleSetLabel as Cint64
            || label_type == LabelCacheItemType::DeterministicSameIndividualSetLabel as Cint64
            || label_type == LabelCacheItemType::NondeterministicSameIndividualSetLabel as Cint64
            || label_type == LabelCacheItemType::DeterministicCombinedDataInstantiatedRoleSetLabel as Cint64
            || label_type
                == LabelCacheItemType::NondeterministicCombinedDataInstantiatedRoleSetLabel as Cint64
        {
            return true;
        }
        false
    }

    /// Port of `CBackendRepresentativeMemoryCache::getIndividualAssociationsExtensionData`
    /// (cpp 3380).
    ///
    /// Lazily creates and returns the `INDIVIDUAL_ASSOCIATION_MAP` extension data of
    /// a label item (the per-label individual-id association set).
    pub fn get_individual_associations_extension_data(
        &mut self,
        label_item: LabelCacheItemId,
        ontology_data: OntologyDataId,
    ) -> LabelCacheItemExtensionDataId {
        // W6-DEFER[api]: faithful body:
        //   context = ctx.ontology(ontologyData).get_ontology_context();
        //   extensionData = ctx.label(label_item).get_extension_data(INDIVIDUAL_ASSOCIATION_MAP);
        //   if !extensionData {
        //     extensionData = ctx.alloc_extension_data(IndividualAssociationMap{ context });
        //     ctx.label(label_item).set_extension_data(INDIVIDUAL_ASSOCIATION_MAP, extensionData);
        //   }
        //   return extensionData;
        let _ = (label_item, ontology_data);
        Id::NONE
    }

    /// Port of `CBackendRepresentativeMemoryCache::getIndividualNeighbourArrayIndexExtensionData`
    /// (cpp 3391).
    ///
    /// Lazily creates and returns the `INDIVIDUAL_NEIGHBOUR_ARRAY_INDEX` extension
    /// data of a label item (initialising the neighbour-array index over the label).
    pub fn get_individual_neighbour_array_index_extension_data(
        &mut self,
        label_item: LabelCacheItemId,
        ontology_data: OntologyDataId,
    ) -> LabelCacheItemExtensionDataId {
        // W6-DEFER[api]: faithful body:
        //   context = ctx.ontology(ontologyData).get_ontology_context();
        //   extensionData = ctx.label(label_item).get_extension_data(INDIVIDUAL_NEIGHBOUR_ARRAY_INDEX);
        //   if !extensionData {
        //     extensionData = ctx.alloc_extension_data(NeighbourArrayIndex{ context, .. });
        //     ctx.label(label_item).set_extension_data(INDIVIDUAL_NEIGHBOUR_ARRAY_INDEX, extensionData);
        //     extensionData.init_neighbour_array_index_data(label_item);
        //   }
        //   return extensionData;
        let _ = (label_item, ontology_data);
        Id::NONE
    }

    /// Port of `CBackendRepresentativeMemoryCache::getNeighbourArrayRoleTagResolvingLabelExtensionData`
    /// (cpp 3403).
    ///
    /// Lazily creates the `TAG_RESOLVING_HASH` extension data: builds, from the
    /// neighbour-array index extension, a tag → (label-item, array-index, deterministic)
    /// resolving hash over every neighbour role-set label's cache values
    /// (determinism inferred from the cache-value identifier).
    pub fn get_neighbour_array_role_tag_resolving_label_extension_data(
        &mut self,
        label_item: LabelCacheItemId,
        ontology_data: OntologyDataId,
    ) -> LabelCacheItemExtensionDataId {
        // W6-DEFER[api]: faithful body (≈30 lines):
        //   context = ctx.ontology(ontologyData).get_ontology_context();
        //   extensionData = ctx.label(label_item).get_extension_data(TAG_RESOLVING_HASH);
        //   if !extensionData {
        //     extensionData = ctx.alloc_extension_data(TagLabelResolving{ context, .. });
        //     ctx.label(label_item).set_extension_data(TAG_RESOLVING_HASH, extensionData);
        //     extensionData.init_tag_label_resolving_extension_data();
        //     indexExtensionData = self.get_individual_neighbour_array_index_extension_data(label_item, ontologyData);
        //     for i in 0..indexExtensionData.get_array_size() {
        //       neighbourRoleSetLabelItem = indexExtensionData.get_neighbour_role_set_label(i);
        //       for labelValueLinker in neighbourRoleSetLabelItem.cache_value_linkers() {
        //         cacheValue = labelValueLinker.get_data();
        //         identifier = cacheValue.get_cache_value_identifier();
        //         nondeterministc = identifier in {
        //             CacheValTagAndNondeterministicRole, CacheValTagAndNondeterministicInversedRole,
        //             CacheValTagAndNondeterministicAssertedRole, CacheValTagAndNondeterministicInversedAssertedRole,
        //             CacheValTagAndNondeterministicNominalConnectedRole,
        //             CacheValTagAndNondeterministicInversedNominalConnectedRole };
        //         linker = ctx.alloc_tag_label_resolving_data_linker();
        //         linker.init_tag_label_resolving_data(neighbourRoleSetLabelItem, i, !nondeterministc);
        //         extensionData.append_tag_label_resolving_data_linker(cacheValue.get_tag(), linker);
        //       }
        //     }
        //   }
        //   return extensionData;
        let _ = (label_item, ontology_data);
        Id::NONE
    }

    /// Port of `CBackendRepresentativeMemoryCache::getMinimumSlotReferreringInstalledValidRecomputationId`
    /// (cpp 3435).
    ///
    /// Returns the minimum, across every published slot, of that slot's ontology
    /// data's minimum-valid-recomputation-id. Loops the facade slot chain
    /// (`self.slot_linker`); resolving a `SlotItemId` to its ontology data needs the
    /// slot arena.
    pub fn get_minimum_slot_referrering_installed_valid_recomputation_id(
        &self,
        ontology_data: OntologyDataId,
    ) -> Cint64 {
        let mut min_installed_valid_rec_id: Cint64 = Cint64::MAX; // CINT64_MAX
        // W6-DEFER[api]: ontology_identifier = ctx.ontology(ontology_data).get_ontology_identifer();
        for _slot_linker_it in &self.slot_linker {
            // W6-DEFER[api]:
            //   referredOntologyData = ctx.slot(_slot_linker_it).get_ontology_data(ontology_identifier);
            //   minValidRecId = ctx.ontology(referredOntologyData).get_minimum_valid_recomputation_id();
            //   min_installed_valid_rec_id = min(min_installed_valid_rec_id, minValidRecId);
        }
        let _ = ontology_data;
        min_installed_valid_rec_id
    }

    /// Port of `CBackendRepresentativeMemoryCache::processCustomsEvents` (cpp 3484–3957).
    ///
    /// The cross-thread event dispatcher: drains the four cache-write / retrieval /
    /// init / report event kinds the worker threads post. Ported as a faithful
    /// dispatch (`type` matched against the `CacheSettings.h` event-type constants in
    /// `value::event`); each branch's installation body is arena/event-payload bound
    /// and deferred, with the C++ operation sequence preserved.
    ///
    /// KONCLUDE-PORT-NOTE[threading]: `type` is a `QEvent::Type` (an int) and `event`
    /// a `CCustomEvent*` (opaque `Cint64`); the staged single-thread port runs the
    /// dispatch inline. The `CThread::processCustomsEvents` base call (timer/quit
    /// infra) is W6-DEFER (the base returns false for our custom types).
    pub fn process_customs_events(&mut self, type_: Cint64, event: Cint64) -> bool {
        // [threading] W6-DEFER[api]: if CThread::processCustomsEvents(type, event) { return true; }
        // (the infra base handles only its own timer/quit events; our custom ids
        // fall through to the branches below).

        if type_ == value::event::REPORT_MAXIMUM_HANDLED_RECOMPUTATION_ID {
            // W6-DEFER[api]:
            //   rmhrie = (CReportMaximumHandledRecomputationIdsEvent*)event;
            //   maxHandledRecomId = rmhrie.getMaximumHandledRecomputationId();
            //   ontologyIdentifier = rmhrie.getOntologyIdentifier();
            //   ontologyData = self.ontology_identifier_data_hash.get(ontologyIdentifier);
            //   if ontologyData {
            //     ctx.ontology(ontologyData).set_next_update_minimum_valid_recomputation_id(maxHandledRecomId + 1);
            //     LOG(...handled recomputation id...);
            //   }
            self.stat_reported_maximum_handled_recomputation_id_count += 1;
            let _ = event;
            return true;
        } else if type_ == value::event::INITIALIZE_INDIVIDUALS_ASSOCIATIONS_CACHE {
            // W6-DEFER[api]:
            //   iiace = (CInitializeIndividualAssociationsCacheEvent*)event;
            //   indiCount = iiace.getIndividualCount(); ontologyIdentifier = iiace.getOntologyIdentifier();
            //   self.prepare_ontology_data_update(ontologyIdentifier, indiCount);
            let _ = event;
            return true;
        } else if type_ == value::event::RETRIEVE_INCOMPLETELY_ASSOCIATION_CACHED {
            self.checking_remaining_incompletely_handled_count += 1;
            // W6-DEFER[api]: the full retrieval-coordination body (cpp 3513–3762, ≈250 lines):
            //   iace = (CRetrieveIncompletelyAssociationCachedEvent*)event;
            //   resolve ontologyData (mOntologyIdentifierDataHash); if found && !association_completed:
            //     inc_incompletely_handled_individuals_retrieval_count;
            //     compute approximate correction counts from last/new coordination hashes;
            //     copy-over kept entries from lastRetrievalHash (unless refill);
            //     if basic-precomputation mode: scan basic-precompuation vector → newRetrievalHash (or deactivate);
            //     else: scan problematic-incompletely-handled set, then from lastMinIncompletelyHandledIndiId,
            //           then a correction full scan, filling newRetrievalHash with insufficiently-handled ids;
            //     if all_individuals_added && first not yet retrieved && !slot_update_integrated: updateSlot = true;
            //     forceCompletion when mConfMaxIncompletelyHandledIndividualsRetrievalCount exceeded;
            //     self.check_association_complete(ontologyData, forceCompletion);
            //   callbackData = iace.getCallback(); if callbackData { callbackData.doCallback(); }
            //   if updateSlot {
            //     ctx.ontology(ontologyData).set_next_slot_update_waiting_count(self.slot_update_waiting_increase_count);
            //     self.create_reader_slot_update(ontologyData, &self.context);
            //     self.clean_unused_slots(&self.context);
            //   }
            let _ = event;
            return true;
        } else if type_ == value::event::WRITE_BACKEND_ASSOCIATION_ENTRY {
            // [threading]: if self.stat_collect_statistics { self.pending_update_count -= 1; /* QAtomicInt::deref */ }
            self.current_update_handling_recomputation_id = -1;
            // W6-DEFER[api]: the full write-installation body (cpp 3765–3951, ≈190 lines):
            //   wcde = (CWriteBackendAssociationCachedEvent*)event;
            //   memoryPools = wcde.getMemoryPools(); newWriteData = wcde.getWriteData();
            //   ontologyIdentifier = newWriteData.getOntologyIdentifier();
            //   ontologyData = mOntologyIdentifierDataHash[ontologyIdentifier]; mLastHandledOntologyContext = ontologyData;
            //   if !ontologyData || !association_completed:
            //     inc_cache_data_update_writing_count; self.write_data_count += 1;
            //     ontologyData = self.prepare_ontology_data_update(ontologyIdentifier);
            //     for each LabelAssociation write-data in the chain:
            //       self.current_update_handling_recomputation_id = baAsWrDa.getRecompuationId();
            //       self.install_temporary_labels(tempLabelWriteDataLinker, ontologyData);
            //       self.install_temporary_cardinalities(tempCardWriteDataLinker, ontologyData);
            //       self.tmp_indi_assoc_prev_update_id = self.next_indi_update_id;
            //       self.tmp_indi_indirectly_conn_nom_label_item_hash.clear();
            //       if self.check_update_rejection(tempAssWriteDataLinker, ontologyData) {
            //         cached |= self.handle_update_rejection(tempAssWriteDataLinker, ontologyData);
            //       } else {
            //         cached |= self.integrate_propagation_cut(tmpPropCutDataLinker, ontologyData);
            //         self.analyse_deterministic_same_as_association_installation(tempAssWriteDataLinker, ontologyData);
            //         cached |= self.install_association_updates(tempAssWriteDataLinker, ontologyData);
            //         cached |= self.install_nominal_indirect_conncetion_updates(tempNomIndirectConnDataLinker, ontologyData);
            //         cached |= self.check_association_usage(tempAssUseDataLinker, ontologyData);
            //         cached |= self.update_involved_individuals(tmpInvolvedIndiDataLinker, ontologyData);
            //         cached |= self.install_deterministic_same_as_association_updates(tempAssWriteDataLinker, ontologyData);
            //         self.deterministic_same_handling_installation_data_hash.clear();
            //         self.propagation_cut_indi_set.clear();
            //         if !self.tmp_det_same_merging_completion_reference_hash.is_empty() {
            //           cached |= self.complete_deterministic_same_as_merging_information(
            //               &mut self.tmp_det_same_merging_completion_reference_hash, ontologyData);
            //           self.tmp_det_same_merging_completion_reference_hash.clear();
            //         }
            //         if !self.tmp_complete_neighbour_same_indi_merging_set.is_empty() {
            //           cached |= self.complete_neighbours_for_same_as_merging(
            //               &mut self.tmp_complete_neighbour_same_indi_merging_set, ontologyData);
            //           self.tmp_complete_neighbour_same_indi_merging_set.clear();
            //         }
            //         drop+clear self.tmp_prop_cut_indi_array_neighbours_handling_data_hash;
            //       }
            //     if !oneCachingSuccess { self.empty_write_data_count += 1; }
            //     forceCompletion when mConfMaxCacheDataUpdateWritingCount exceeded;
            //     self.check_association_complete(ontologyData, forceCompletion);
            //     if self.check_basic_precompuation_mode_activation(ontologyData)
            //        && self.activate_basic_precompuation_mode(ontologyData) { basicPrecomputationModeActivated = true; }
            //     if next_slot_update_waiting_count <= 0 || association_completed || basicPrecomputationModeActivated {
            //       self.delete_expired_individual_association_memory_contexts(ontologyData, &self.context);
            //       self.create_reader_slot_update(ontologyData, &self.context);
            //       self.clean_unused_slots(&self.context);
            //       set_next_slot_update_waiting_count(self.slot_update_waiting_increase_count); self.slot_update_waiting_increase_count += 1;
            //       clamp to self.slot_update_waiting_max_count; slotUpdate = true;
            //     } else { dec next_slot_update_waiting_count; }
            //     LOG(update/statistics...);
            //   else: LOG("Ignoring update since individual label association is already complete.");
            //   self.cache_stat.set_memory_consumption(self.context.get_memory_consumption());
            //   if self.limit_remaining_write_pending { self.remaining_write_pending_semaphore.release(); /* [threading] */ }
            let _ = event;
            return true;
        }
        false
    }
}
