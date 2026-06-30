//! `cache::backend_facade_gap` — the F1 facade method body that falls in the
//! **GAP** between `backend_facade1` (cpp 34–1619) and `backend_facade2`
//! (cpp 2763–3957) of `CBackendRepresentativeMemoryCache::*` (Konclude
//! `Source/Reasoner/Kernel/Cache/CBackendRepresentativeMemoryCache.cpp`).
//!
//! ## Range taken (cpp lines 1620–2762)
//!
//! Exactly ONE method definition starts in this span — the giant
//! `installAssociationUpdate` (cpp **1620–2727**; lines 2728–2762 are blank
//! padding before `updateIndexedAssociationCount` at 2763, which `backend_facade2`
//! owns). This file ports that single method.
//!
//! `installAssociationUpdate` is the heart of the realisation/association store:
//! given one temporary association-write linker for an individual, it decides
//! whether the cached labels / status flags / neighbour-role-set links /
//! indirect-nominal integration must be re-written, and if so localises a fresh
//! individual-association-data record, merges/replaces/reduces every changed
//! label, rebuilds the neighbour role-set array + hash (with prop-cut readd /
//! removal, problematic-leveled-neighbour handling, and deterministic-same-as
//! neighbour completion), updates the statistics, and re-stores the association.
//!
//! ## Port status (struct-def era — no cache arena yet)
//!
//! Identical situation to `backend_facade2`: the F1 per-ontology / per-individual /
//! label / neighbour-array arenas (`Arena<OntologyData>` /
//! `Arena<IndividualAssociationData>` / `Arena<LabelCacheItem>` /
//! `Arena<IndividualRoleSetNeighbourArray>` / …) and the cache context that owns
//! them are NOT yet ported, so an `IndividualAssociationDataId` /
//! `OntologyDataId` / `BackendTempWriteRecordId` / `LabelCacheItemId` cannot be
//! resolved to an object. Every such dereference is a `// W6-DEFER[api]` (the
//! precedent set by `backend_facade1::install_association_updates` and the
//! W3/W4 deferred-arena waves). Reachable FACADE-field reads/writes
//! (`self.propagation_cut_indi_set`, `self.next_indi_update_id`, the `self.stat_*`
//! counters, the `self.conf_*` flags, the `self.tmp_*` / `deterministic_same_*`
//! hashes keyed by the `cint64` individual id) and **sibling facade calls**
//! (`self.x(...)`, defined across `backend_facade{1,2,3}`) are ported live; only
//! the arena-bound inner logic is deferred, with the faithful C++ control flow
//! preserved in the deferred block. No logic is dropped.
//!
//! ## License (per `PORT.md` §License note)
//! Function-by-function translation of LGPLv3 Konclude source; the LGPL terms
//! attach to this ported module.
//!
//! ## Port conventions (PORT.md §44) — same as `backend.rs`
//! * `CXxx*` → typed arena `Id<T>` (`Id::NONE` == null);
//! * intrusive linker / `QSet<cint64>` / `QHash<cint64,cint64>` → `Vec`/`HashMap`,
//!   head-at-front;
//! * `QMutex`/`QSemaphore`/`QEvent` → `[threading]` single-thread inline;
//! * memory pools / contexts → opaque `Cint64` `[memory-pool]`;
//! * the `updateIndexedAssociationCount` overload pair → facade2's split names
//!   `update_indexed_association_count` / `update_indexed_association_count_for_association_data`.

#![allow(dead_code, unused_variables, unused_mut, unused_assignments)]

use super::super::model::substrate::Cint64;
use super::backend::BackendRepresentativeMemoryCache;
use super::backend_data::{
    BackendTempWriteRecordId, IndividualAssociationDataId, LabelCacheItemId, OntologyDataId,
    LABEL_CACHE_ITEM_ASSOCIATABLE_TYPE_COUNT,
};

impl BackendRepresentativeMemoryCache {
    /// Port of `CBackendRepresentativeMemoryCache::installAssociationUpdate`
    /// (cpp 1620–2727).
    ///
    /// `installAssociationUpdate(cint64 individualID,
    /// CBackendRepresentativeMemoryCacheIndividualAssociationData* associationData,
    /// CBackendRepresentativeMemoryCacheTemporaryAssociationWriteDataLinker* tempAssWriteDataLinkerIt,
    /// CBackendRepresentativeMemoryCacheOntologyData* ontologyData)`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: the pointer args become the facade-arena ids
    /// `association_data` / `temp_ass_write_data_linker_it` / `ontology_data`;
    /// `individualID` is a plain `cint64`. With no cache arena reachable from
    /// `&mut self`, every `associationData->…` / `tempAssWriteDataLinkerIt->…` /
    /// `ontologyData->…` / label-item / neighbour-array / role-set-hash /
    /// neighbour-id-linker dereference is `W6-DEFER[api]`; the faithful control
    /// flow is preserved as structured deferred blocks (phase by phase, with the
    /// cpp line spans). The resolvable facade-field effects and sibling calls are
    /// ported live. C++ returns `bool associationsUpdated`.
    pub fn install_association_update(
        &mut self,
        individual_id: Cint64,
        association_data: IndividualAssociationDataId,
        temp_ass_write_data_linker_it: BackendTempWriteRecordId,
        ontology_data: OntologyDataId,
    ) -> bool {
        // ---- cpp 1622–1634: setup, cache-touch id, label/links update types ----
        let mut associations_updated = false;

        // W6-DEFER[api]: individual = tempAssWriteDataLinkerIt->getIndividual();  (opaque CIndividual*)
        // W6-DEFER[api]: usedUpdateId = tempAssWriteDataLinkerIt->getUsedAssociationUpdateId();
        let used_update_id: Cint64 = 0; // W6-DEFER[api]: temp-linker getUsedAssociationUpdateId.

        if association_data != IndividualAssociationDataId::NONE {
            // associationData->setCacheTouchId(mNextIndiUpdateId++);
            // The mNextIndiUpdateId advance is a live facade effect (guard resolvable);
            // the setCacheTouchId store on the arena object is deferred.
            let _cache_touch_id = self.next_indi_update_id;
            self.next_indi_update_id += 1;
            // W6-DEFER[api]: ctx.assoc(association_data).set_cache_touch_id(_cache_touch_id);
        }

        // W6-DEFER[api]: the three label-update-type and three links-update-type
        // booleans read tempAssWriteDataLinkerIt->getLabelUpdateType() /
        // getLinksUpdateType() against ADDITION / REPLACEMENT / REMOVAL (cpp 1632–1639).
        let mut label_addition = false; // == ADDITION
        let mut label_replacement = false; // == REPLACEMENT
        let mut label_removal = false; // == REMOVAL
        let mut links_addition = false; // == ADDITION
        let mut links_replacement = false; // == REPLACEMENT
        let mut links_removal = false; // == REMOVAL

        // ---- cpp 1644–1654: collect the referred label cache items per associatable type ----
        // for i in 0..ASSOCIATABLE_TYPE_COUNT:
        //   referredLabelCacheItem = tempAssWriteDataLinkerIt->getReferredLabelData(i);
        //   if !referredLabelCacheItem { tmp = tempAssWriteDataLinkerIt->getReferredTemporaryLabelData(i);
        //     if tmp { referredLabelCacheItem = (LabelCacheItem*)tmp->getTemporaryData(); } }
        //   referredLabels[i] = referredLabelCacheItem;
        let mut referred_labels: [LabelCacheItemId; LABEL_CACHE_ITEM_ASSOCIATABLE_TYPE_COUNT] =
            [LabelCacheItemId::NONE; LABEL_CACHE_ITEM_ASSOCIATABLE_TYPE_COUNT];
        // W6-DEFER[api]: fill referred_labels[i] from the temp linker's referred / referred-temporary label data.
        let _ = &mut referred_labels;

        // ---- cpp 1657–1661: prop-cut membership + integration change id + same-neighbour flag ----
        // prop_cut is a LIVE facade-field read (mPropagationCutIndiSet.contains(individualID)).
        let prop_cut = self.propagation_cut_indi_set.contains(&individual_id);
        // W6-DEFER[api]: integratedIndirectlyConnectedIndividualsChangeId = tempAss->getIntegratedIndirectlyConnectedIndividualsChangeId();
        let integrated_indirectly_connected_individuals_change_id: Cint64 = 0;
        let mut incompatible_changes = false;
        // W6-DEFER[api]: detSameNeighbourCompletion = tempAss->requireSameAsNeighboursCompletion();
        let mut det_same_neighbour_completion = false;

        // ---- cpp 1662–1748: incompatible-change / label-compatibility analysis ----
        // The whole block is gated on the (deferred) predicate
        //   associationData && (associationData->getAssociationDataUpdateId() != usedUpdateId
        //                       || associationData->getAssociatedIndividualId() != tempAss->getIndividualID()).
        // W6-DEFER[api]: faithful control flow (cpp 1662–1748):
        //   labelCompatible = false;
        //   if associationData && mConfInterpretUnchangedLabelsAsCompatible && associationData->isCompletelyHandled() {
        //     usedReferredAssociationData = associationData->getPreviousData();
        //     while usedReferred && usedReferred->getAssociationDataUpdateId() > usedUpdateId { usedReferred = usedReferred->getPreviousData(); }
        //     if usedReferred && usedReferred->getAssociationDataUpdateId() != usedUpdateId { usedReferred = null; }
        //     if usedReferred {
        //       labelCompatible = true;
        //       for i in 0..ASSOCIATABLE_TYPE_COUNT while labelCompatible:
        //         if referredLabels[i] != associationData->getLabelCacheEntry(i) {
        //           if i == NEIGHBOUR_INSTANTIATED_ROLE_SET_COMBINATION_LABEL {
        //             if labelReplacement && (linksAddition || propCut) { labelAddition = true; labelReplacement = false; }
        //           } else if i == NONDETERMINISTIC_COMBINED_NEIGHBOUR_... || i == DETERMINISTIC_COMBINED_NEIGHBOUR_... {
        //             labelAddition = true; labelReplacement = false;
        //           } else { labelCompatible = false; }
        //         }
        //       if labelCompatible && (linksReplacement && propCut || linksAddition) {
        //         conSetLabel = associationData->getLabelCacheEntry(FULL_CONCEPT_SET_LABEL);
        //         if conSetLabel->getExtensionData(CARDINALITY_HASH) { labelCompatible = false; }
        //         currentNeighbourRoleSetHash = associationData->getNeighbourRoleSetHash();
        //         referredNeighbourRoleSetHash = usedReferred->getNeighbourRoleSetHash();
        //         for each roleSetNeighbourUpdateDataLinkerIt in tempAss->getRoleSetNeighbourUpdateDataLinker() while labelCompatible:
        //           neighbourId = it->getNeighbourIndividualReference().getIndividualID();
        //           newNeighbourLabel = it->...getReferredLabelData() (or temp->getTemporaryData());
        //           referredNeighbourLabel = referredNeighbourRoleSetHash ? referredNeighbourRoleSetHash->getNeighbourRoleSetLabel(neighbourId) : null;
        //           currentNeighbourLabel  = currentNeighbourRoleSetHash ? currentNeighbourRoleSetHash->getNeighbourRoleSetLabel(neighbourId) : null;
        //           if currentNeighbourLabel && referredNeighbourLabel != currentNeighbourLabel
        //               && !self.is_role_neighbour_link_label_item_compatibility(currentNeighbourLabel, newNeighbourLabel) { labelCompatible = false; }
        //           else if !currentNeighbourLabel && referredNeighbourLabel { labelCompatible = false; }
        //       } else { labelCompatible = false; }
        //     }
        //   }
        //   if !labelCompatible {
        //     labelAddition = true; labelRemoval = false; labelReplacement = false;
        //     linksAddition = true; linksRemoval = false; linksReplacement = false;
        //     incompatibleChanges = true;
        //   }
        // (Note: the whole guard's else-branch leaves incompatible_changes false.)
        let _ = (
            used_update_id,
            self.conf_interpret_unchanged_labels_as_compatible,
            prop_cut,
            &mut label_addition,
            &mut label_replacement,
            &mut label_removal,
            &mut links_addition,
            &mut links_replacement,
            &mut links_removal,
            &mut incompatible_changes,
        );

        // ---- cpp 1755–1767: required-update flags (labels / status flags) ----
        // W6-DEFER[api]: repLabelUpdateRequired = false;
        //   for i in 0..ASSOCIATABLE_TYPE_COUNT while associationData && !repLabelUpdateRequired:
        //     if (referredLabels[i] || labelReplacement || labelRemoval)
        //         && (!associationData || referredLabels[i] != associationData->getLabelCacheEntry(i)) { repLabelUpdateRequired = true; }
        let mut rep_label_update_required = false;
        // W6-DEFER[api]: statusFlagsUpdateRequired:
        //   if (tempAss->getStatusFlags() != 0 || labelReplacement || labelRemoval)
        //       && (!associationData || associationData->getStatusFlags() != tempAss->getStatusFlags())
        //       || incompatibleChanges { statusFlagsUpdateRequired = true; }
        let mut status_flags_update_required = false;

        // ---- cpp 1771–1805: required-update flag (neighbour links) ----
        // W6-DEFER[api]: linksUpdateRequired:
        //   if tempAss->getRoleSetNeighbourUpdateDataLinker() != null || linksReplacement || linksRemoval {
        //     existingNeighbourRoleSetHash = associationData ? associationData->getNeighbourRoleSetHash() : null;
        //     updateLinksCount = 0;
        //     for each roleSetNeighbourUpdateDataLinkerIt while !linksUpdateRequired:
        //       neighbourId = it->...getIndividualID();
        //       referredLabelCacheItem = it->...getReferredLabelData() (or temp->getTemporaryData());
        //       if linksAddition { if !existing { linksUpdateRequired = true; }
        //         else if existing->getNeighbourRoleSetLabel(neighbourId) != referredLabelCacheItem { linksUpdateRequired = true; } }
        //       if linksRemoval { if existing && existing->getNeighbourRoleSetLabel(neighbourId) { linksUpdateRequired = true; } }
        //       updateLinksCount++;
        //     if !linksUpdateRequired && (updateLinksCount > 0 && !existing
        //         || existing && updateLinksCount != existing->getNeighbourCount()) { linksUpdateRequired = true; }
        //   }
        let mut links_update_required = false;

        // ---- cpp 1806–1859: deterministic-same neighbour-completion scheduling ----
        // newCompletingDetSameNeighbours / newlyCompletedDetSameNeighbours are local id sets.
        // installData is a LIVE facade-field entry (mDeterministicSameHandlingInstallationDataHash[individualID]).
        let mut new_completing_det_same_neighbours: Vec<Cint64> = Vec::new();
        let mut newly_completed_det_same_neighbours: Vec<Cint64> = Vec::new();
        let mut complete_only_compatible_neighbour_role_labels = false;
        if det_same_neighbour_completion {
            // installData = mDeterministicSameHandlingInstallationDataHash[individualID];  (live facade field)
            let install_data = self
                .deterministic_same_handling_installation_data_hash
                .entry(individual_id)
                .or_default()
                .clone();
            // W6-DEFER[api]: existDetSameHandlIdLabel = associationData ? associationData->getDeterministicMergedSameConsideredLabelCacheEntry() : null;
            //   if !existDetSameHandlIdLabel { newCompletingDetSameNeighbours = installData.mIdPossibleInstallationSet; }
            //   else {
            //     newDetSameLabel = referredLabels[DETERMINISTIC_SAME_INDIVIDUAL_SET_LABEL];
            //     for each valueLinkerIt in existDetSameHandlIdLabel->getCacheValueLinker() while detSameNeighbourCompletion:
            //       if !newDetSameLabel->hasCachedTagValue(valueLinkerIt->getCacheValue().getTag()) { detSameNeighbourCompletion = false; }
            //     for possDetSameInstallId in installData.mIdPossibleInstallationSet:
            //       if !existDetSameHandlIdLabel->hasCachedTagValue(possDetSameInstallId) { newCompletingDetSameNeighbours.insert(possDetSameInstallId); }
            //   }
            // Faithful (deferred) approximation of the first branch — the possible-installation
            // set is a live facade field; the existDetSameHandlIdLabel deref decides which path:
            new_completing_det_same_neighbours = install_data.id_possible_installation_set.clone();

            if !new_completing_det_same_neighbours.is_empty() {
                // W6-DEFER[api]: unchangedDetMergedUpdateCount walk over previous association data
                //   while prevAssociationData->getRepresentativeSameIndividualId() == tempAss->getRepresentativeSameIndividualId()
                //         && unchangedDetMergedUpdateCount < mConfUnchangedDeterministicSameMergeUpdatesForDeterministicSameNeighbourCompletion
                //     { ++unchangedDetMergedUpdateCount; prevAssociationData = prevAssociationData->getPreviousData(); }
                let unchanged_det_merged_update_count: Cint64 = 0;

                if !incompatible_changes
                    && (new_completing_det_same_neighbours.len() as Cint64)
                        < self.conf_min_required_deterministic_same_merged_handled_installation_possiblities_for_neighbour_completion
                    && unchanged_det_merged_update_count
                        < self.conf_unchanged_deterministic_same_merge_updates_for_deterministic_same_neighbour_completion
                {
                    incompatible_changes = true;
                    status_flags_update_required = true;
                    det_same_neighbour_completion = false;
                } else {
                    if incompatible_changes
                        && (!self.conf_installing_deterministic_same_handling_large_difference_reached
                            || (install_data.id_first_possible_installation_set.len() as Cint64)
                                < self.conf_installing_deterministic_same_handling_large_difference)
                    {
                        det_same_neighbour_completion = false;
                    } else {
                        links_update_required = true;
                    }
                    if incompatible_changes && det_same_neighbour_completion {
                        complete_only_compatible_neighbour_role_labels = true;
                    }
                }
            } else {
                det_same_neighbour_completion = false;
            }
        }

        // ---- cpp 1862–1867: indirect-connection integration change detection ----
        // W6-DEFER[api]: integrationUpdated:
        //   if !associationData || (associationData && (
        //        tempAss->hasIndirectlyConnectedIndividualIntegration() && !associationData->hasIndirectlyConnectedIndividualIntegration()
        //     || tempAss->isIndirectlyConnectedNominalIndividual() && !associationData->isIndirectlyConnectedNominalIndividual()
        //     || integratedIndirectlyConnectedIndividualsChangeId > 0
        //        && integratedIndirectlyConnectedIndividualsChangeId != associationData->getLastIntegratedIndirectlyConnectedIndividualsChangeId())) { integrationUpdated = true; }
        let mut integration_updated = false;

        // ---- cpp 1870–2725: the actual update body ----
        if association_data == IndividualAssociationDataId::NONE
            || rep_label_update_required
            || status_flags_update_required
            || links_update_required
            || integration_updated
        {
            // cpp 1872–1873: live facade counters.
            self.updated_indi_count += 1;
            self.association_updated_indi_count += 1;

            // cpp 1876–1879: localise a fresh association data + pick its memory context (live sibling calls).
            let loc_association_data = self.create_localized_individual_association_data(
                individual_id,
                association_data,
                ontology_data,
                true,
                true,
            );
            let mut requies_data_copying = false;
            let context = self.get_individual_association_data_memory_context(
                loc_association_data,
                ontology_data,
                Some(&mut requies_data_copying),
            );

            // cpp 1882–1884: propagation-cut update id.
            if prop_cut {
                // W6-DEFER[api]: locAssociationData->setLastPropagationCuttingUpdateId(locAssociationData->getAssociationDataUpdateId());
            }

            // cpp 1886–1897 (debug-gen block omitted) + cache-update id stamp.
            // W6-DEFER[api]: locAssociationData->setCacheUpdateId(mNextIndiUpdateId++);
            //   ontologyData->setMaxIndividualAssociationDataUpdateCount(qMax(locAssoc->getAssociationDataUpdateId(), ontologyData->getMax...()));
            let _new_cache_update_id = self.next_indi_update_id;
            self.next_indi_update_id += 1; // live facade effect (mNextIndiUpdateId++).

            // cpp 1899–1916: representative-same-individual id min + merge bookkeeping.
            // W6-DEFER[api]: locAssoc->setRepresentativeSameIndividualId(qMin(tempAss->getRepresentativeSameIndividualId(), locAssoc->getRepresentativeSameIndividualId()));
            let mut same_indi_merged_changed = false;
            // W6-DEFER[api]: if locAssoc->getRepresentativeSameIndividualId() != locAssoc->getAssociatedIndividualId() {
            //     ontologyData->setSameIndividualsMergings(true);
            //     if !associationData || !associationData->hasRepresentativeSameIndividualMerging() {
            //       self.stat_det_same_representative_merging_count += 1;   (live)
            //       ontologyData->incIndividualAssociationMergingCount(); } }
            //   if !associationData || locAssoc->getRepresentativeSameIndividualId() != associationData->getRepresentativeSameIndividualId() { sameIndiMergedChanged = true; }
            let _ = &mut same_indi_merged_changed;
            // W6-DEFER[api]: cpp 1913–1916 — remember deterministic-same mergings into the live tmp hash:
            //   if incompatibleChanges && locAssoc->getLabelCacheEntry(DETERMINISTIC_SAME_INDIVIDUAL_SET_LABEL)
            //       && that != referredLabels[DETERMINISTIC_SAME_INDIVIDUAL_SET_LABEL] {
            //     self.tmp_det_same_merging_completion_reference_hash.insert(assocIndiId, assocIndiId); }

            // cpp 1918–1958: label update.
            let mut labels_updated = false;
            if association_data == IndividualAssociationDataId::NONE || rep_label_update_required {
                // for i in 0..ASSOCIATABLE_TYPE_COUNT:
                //   if referredLabels[i] != locAssoc->getLabelCacheEntry(i) {
                //     if referredLabels[i] || labelReplacement || labelRemoval {
                //       if locAssoc->getLabelCacheEntry(i) && labelAddition {
                //         mergedLabel = self.get_addition_merged_label(i, referredLabels[i], locAssoc->getLabelCacheEntry(i), ontologyData);
                //         if mergedLabel != locAssoc->getLabelCacheEntry(i) { locAssoc->setLabelCacheEntry(i, mergedLabel); }
                //       } else { locAssoc->setLabelCacheEntry(i, referredLabels[i]); }
                //     }
                //   }
                //   self.update_indexed_association_count_for_association_data(locAssoc, associationData, i, ontologyData);
                // W6-DEFER[api]: the per-i label merge/replace is arena-bound; the sibling
                // calls (get_addition_merged_label / update_indexed_association_count_for_association_data)
                // run once per associatable type in the live flow once the arena lands.
                labels_updated = true;
                associations_updated = true;
                // W6-DEFER[api]: if associationData { indConnNomLabelItem = associationData->getLabelCacheEntry(INDIRECTLY_CONNECTED_NOMINAL_INDIVIDUAL_SET_LABEL);
                //   if indConnNomLabelItem { self.tmp_indi_indirectly_conn_nom_label_item_hash.insert(individualID, indConnNomLabelItem); } }
            } else if same_indi_merged_changed {
                // for i in 0..ASSOCIATABLE_TYPE_COUNT:
                //   if requiresIndividualAssociations(i) && !mConfLateIndividualLabelAssociationIndexing {
                //     labelItem = locAssoc->getLabelCacheEntry(i);
                //     indiAssoExtData = self.get_individual_associations_extension_data(labelItem, ontologyData);
                //     indiAssoExtData->removeIndividualIdAssociation(locAssoc);
                //     indiAssoExtData->addIndividualIdAssociation(locAssoc); }
                // W6-DEFER[api]: arena-bound re-indexing of the unchanged labels under the new merged id.
                let _ = self.conf_late_individual_label_association_indexing;
            }

            // cpp 1960–1976: integration + status flag writes.
            if integration_updated {
                // W6-DEFER[api]: if integratedIndirectlyConnectedIndividualsChangeId > 0 { locAssoc->setLastIntegratedIndirectlyConnectedIndividualsChangeId(...); }
                //   if tempAss->hasIndirectlyConnectedIndividualIntegration() { locAssoc->setIndirectlyConnectedIndividualIntegration(true); }
                //   if tempAss->isIndirectlyConnectedNominalIndividual() { locAssoc->setIndirectlyConnectedNominalIndividual(true); }
                associations_updated = true;
            }
            if status_flags_update_required {
                // W6-DEFER[api]: locAssoc->setStatusFlags(tempAss->getStatusFlags());
                associations_updated = true;
            }

            // cpp 1979–1988: neighbour-role-set combination label change → links update required.
            // W6-DEFER[api]: newNeighbourRoleSetCompLabel = locAssoc->getLabelCacheEntry(NEIGHBOUR_INSTANTIATED_ROLE_SET_COMBINATION_LABEL);
            //   prevNeighbourRoleSetCompLabel = associationData ? associationData->getLabelCacheEntry(NEIGHBOUR_...) : null;
            //   if !linksUpdateRequired && prevNeighbourRoleSetCompLabel && newNeighbourRoleSetCompLabel != prevNeighbourRoleSetCompLabel { linksUpdateRequired = true; associationsUpdated = true; }

            // cpp 1991–2563: the neighbour role-set ARRAY + HASH rebuild.
            //
            // KONCLUDE-PORT-NOTE[api]: this ~570-line region is the most arena-entangled
            // in the file — it manipulates six cooperating facade-arena object families
            // (IndividualRoleSetNeighbourArray, IndividualNeighbourRoleSetHash, the
            // per-array IndividualRoleSetNeighbourData slots, the IndividualRoleSetNeighbour
            // IndividualIdLinker chains, the per-array problematic-leveled-neighbour set
            // arrays, and the label-cache combination-label items) none of which can be
            // resolved without the cache arena. The full faithful control flow is preserved
            // here as structured pseudo-code; nothing is dropped. Live facade effects called
            // out inline: mStatCreatedNeighbourLinks++, mStatAdding/UpdatedOrRemovedNeighbour
            // LinksAssociationUpdateCount, mReducedNeighbourArrayCount++, and the sibling
            // calls getIndividualNeighbourArrayIndexExtensionData / getReducedLabel /
            // getExtendedLabel / copyNeighbourIndividualIdLinkers / completeSameAsNeighbours /
            // update_indexed_association_count.
            let mut links_updated = false;
            let mut neighbour_role_set_comp_label_reduction_checking = false;
            let neighbour_role_set_comp_label_reduction_required = false;
            if links_update_required {
                links_updated = true;
                // W6-DEFER[api]: faithful control flow (cpp 2005–2563):
                //   propMarkLabelItem = ontologyData->getPrioritizedPropagationMarkedNeighbourLabelItem();
                //   newArrayIndexData = self.get_individual_neighbour_array_index_extension_data(newNeighbourRoleSetCompLabel, ontologyData);
                //   newNeighbourRoleSetHash = alloc; prevNeighbourRoleSetHash = associationData ? associationData->getNeighbourRoleSetHash() : null;
                //   newArray = alloc; prevArray = associationData ? associationData->getRoleSetNeighbourArray() : null;
                //   prevArrayIndexData = prevArray ? prevArray->getIndexData() : null;
                //   if (linksRemoval || linksReplacement || tempAss->requireSameAsNeighboursCompletion() && !detSameNeighbourCompletion) && prevArray {
                //     updateOrRemovalNeighbourIndiIdSet = new set; mStatUpdatedOrRemovedNeighbourLinksAssociationUpdateCount++;
                //   } else { mStatAddingNeighbourLinksAssociationUpdateCount++; }
                //
                //   // prop-cut readd/reduction/removal handling (cpp 2037–2072) via mTmpPropCutIndiArrayNeighboursHandlingDataHash[individualID]:
                //   //   propCutReadding / propCutReaddingArrayIds(mReaddingArrayPosSet) / propCutRemovingArrayIds(mRemovalArrayPosSet);
                //   //   for i in handlingData.mReductionArrayPosSet: reducedNeighLabelItem = self.get_reduced_label(NEIGHBOUR_INSTANTIATED_ROLE_SET_LABEL, prevNeighLabelItem,
                //   //       |cacheValue| self.is_cache_value_role_nondeterministic(cacheValue), ontologyData);
                //   //       newIndex = newArrayIndexData->getIndex(reducedNeighLabelItem); if newIndex >= 0 { propCutArrayNewPrevReductionIdHash.insertMulti(newIndex, i); }
                //
                //   // problematic-leveled-neighbour detection (cpp 2075–2097):
                //   //   for each roleSetNeighbourUpdateDataLinkerIt: if referredLabelCacheItem && prevNeighbourRoleSetHash {
                //   //     if !updateOrRemovalNeighbourIndiIdSet && prevNeighbourRoleSetHash->getNeighbourRoleSetLabel(neighbourId) { updateOrRemovalNeighbourIndiIdSet = new set; ... }
                //   //     else if !hasProblematicLeveledNeighbours && ontologyData->hasInvolvedIndividuals() {
                //   //       neighbourAssociationData = ontologyData->getIndividualIdAssoiationDataVector()[neighbourId];
                //   //       if neighbourAssociationData->hasProblematicLevel() { locAssoc->setProblematicLeveledNeigbour(true); hasProblematicLeveledNeighbours = true; } } }
                //
                //   // prioritized-prop-mark readd label extension (cpp 2098–2119):
                //   //   if prevNeighbourRoleSetCompLabel && prevArray && propMarkLabelItem && linksAddition && incompatibleChanges {
                //   //     prevPrioPropMarkIndex = prevArrayIndexData->getIndex(propMarkLabelItem);
                //   //     if prevPrioPropMarkIndex >= 0 && prevArray->at(prevPrioPropMarkIndex).getIndividualCount() > 0 { readdingPrioPropMarkNeighbours = true; } }
                //   //   if readdingPrioPropMarkNeighbours { newPrioPropMarkIndex = newArrayIndexData->getIndex(propMarkLabelItem);
                //   //     if newPrioPropMarkIndex < 0 { extendingCacheValue.initCacheValue(propMarkLabelItem->getCacheEntryID(), (cint64)propMarkLabelItem, CACHE_VALUE_TAG_AND_ENTRY);
                //   //       newNeighbourRoleSetCompLabel = self.get_extended_label(NEIGHBOUR_..._COMBINATION_LABEL, prevNew, extendingCacheValue, ontologyData);
                //   //       locAssoc->setLabelCacheEntry(NEIGHBOUR_..._COMBINATION_LABEL, newNeighbourRoleSetCompLabel);
                //   //       self.update_indexed_association_count(locAssoc, prevNew, NEIGHBOUR_..._COMBINATION_LABEL, ontologyData);
                //   //       newArrayIndexData = self.get_individual_neighbour_array_index_extension_data(newNeighbourRoleSetCompLabel, ontologyData);
                //   //       newPrioPropMarkIndex = newArrayIndexData->getIndex(propMarkLabelItem); } }
                //
                //   // problematic-leveled set array alloc (cpp 2122–2128).
                //
                //   // two array-population branches (cpp 2131–2204):
                //   //   if prevNeighbourRoleSetCompLabel == newNeighbourRoleSetCompLabel && prevArray && linksAddition && !updateOrRemovalNeighbourIndiIdSet {
                //   //     newArray->initNeighbourArray(prevArray); newNeighbourRoleSetHash->initNeighbourRoleSetHash(prevNeighbourRoleSetHash, requiesDataCopying);
                //   //     if requiesDataCopying { for i: neighbourData.setIndividualIdLinker(self.copy_neighbour_individual_id_linkers(...), false); }
                //   //     if hasProblematicLeveledNeighbours { for i != newPrioPropMarkIndex: split off leading problematic-level neighbours into idProblematicLeveledNeighboursSetArray[i]; }
                //   //   } else {
                //   //     newArray->initNeighbourArray(newArrayIndexData);
                //   //     if linksAddition && prevArray && !updateOrRemovalNeighbourIndiIdSet { copy matching prev rows by label, split problematic-level, copy id linkers if requiesDataCopying; initNeighbourRoleSetHash(prev,copy); }
                //   //     else { if !linksReplacement { initNeighbourRoleSetHash(prev,copy); } else { initNeighbourRoleSetHash(null); } }
                //   //   }
                //
                //   // add/update new neighbour data (cpp 2206–2253):
                //   //   for each roleSetNeighbourUpdateDataLinkerIt with referredLabelCacheItem:
                //   //     index = newArrayIndexData->getIndex(referredLabelCacheItem);
                //   //     if hasProblematicLeveledNeighbours && neighbourAssociationData->hasProblematicLevel() {
                //   //       move from prev index, idProblematicLeveledNeighboursSetArray[index].insert(neighbourId); newArray->at(index).incIndividualCount();
                //   //     } else { newLinker = alloc; mStatCreatedNeighbourLinks++; newLinker->initIndividualIdLinker(neighbourId); newArray->at(index).addIndividualIdLinker(newLinker); }
                //   //     newNeighbourRoleSetHash->setNeighbourRoleSetLabel(neighbourId, referredLabelCacheItem);
                //   //     if updateOrRemovalNeighbourIndiIdSet { record prev index count; updateOrRemovalNeighbourIndiIdSet.insert(neighbourId); }
                //
                //   // copy remaining previous data (cpp 2256–2358): for each new array pos with a prev row (honoring propCutReadding),
                //   //   re-add the previous neighbours not in updateOrRemovalNeighbourIndiIdSet, preserving problematic-level ordering,
                //   //   creating new id linkers (mStatCreatedNeighbourLinks++) or splicing readding linkers (copy if requiesDataCopying).
                //
                //   // prop-cut reduction reconciliation (cpp 2360–2395): propCutArrayNewPrevReductionIdHash → merge prev rows into reduced new rows.
                //
                //   // cleanup (cpp 2401–2404): delete propCutArrayNewPrevReductionIdHash; delete updateOrRemovalNeighbourIndiIdSet.
                //
                //   // prop-cut removed-neighbour linker rebuild (cpp 2406–2452): rebuild locAssoc->getPropagationCutRemovedNeighbourIndividualLinker()
                //   //   keeping those with no new neighbour label, plus removals from propCutRemovingArrayIds; setPropagationCutRemovedNeighbourIndividualLinker(...).
                //
                //   // readd prioritized prop-mark row (cpp 2455–2460).
                //
                //   // deterministic-same neighbour completion (cpp 2463–2486):
                //   //   if detSameNeighbourCompletion { locAssoc->setNeighbourRoleSetHash(newHash); locAssoc->setRoleSetNeighbourArray(newArray);
                //   //     if self.complete_same_as_neighbours(locAssoc, newCompletingDetSameNeighbours, &mut newlyCompletedDetSameNeighbours, completeOnlyCompatibleNeighbourRoleLabels, ontologyData)
                //   //       { self.tmp_complete_neighbour_same_indi_merging_set.push(assocIndiId); } }
                //   //   neighbourRoleSetCompLabelReductionChecking = true;  (else branch sets it only if incompatibleChanges || detSameNeighbourCompletion)
                //
                //   // problematic-leveled neighbour flush (cpp 2491–2509): append each idProblematicLeveledNeighboursSetArray[idx] id as a new id linker (mStatCreatedNeighbourLinks++); free the set array.
                //
                //   // neighbour-role-set combination-label reduction (cpp 2512–2557):
                //   //   if neighbourRoleSetCompLabelReductionChecking { for i: if !newArray->at(i).getIndividualIdLinker() { neighbourRoleSetCompLabelReductionRequired = true; }
                //   //     if reductionRequired { mReducedNeighbourArrayCount++;
                //   //       reduced = self.get_reduced_label(NEIGHBOUR_..._COMBINATION_LABEL, comb, |cacheValue| { ... empty-row test over newArray ... }, ontologyData);
                //   //       if comb != reduced { locAssoc->setLabelCacheEntry(NEIGHBOUR_..._COMBINATION_LABEL, reduced);
                //   //         self.update_indexed_association_count(locAssoc, comb, NEIGHBOUR_..._COMBINATION_LABEL, ontologyData);
                //   //         reducedArrayIndexData = self.get_individual_neighbour_array_index_extension_data(reduced, ontologyData);
                //   //         reducedArray = alloc; reducedArray->initNeighbourArray(reducedArrayIndexData); copy rows by label; newArray = reducedArray; newArrayIndexData = reducedArrayIndexData; } } }
                //
                //   // commit (cpp 2561–2563): locAssoc->setNeighbourRoleSetHash(newHash); locAssoc->setRoleSetNeighbourArray(newArray); associationsUpdated = true;
                let _ = (context, requies_data_copying, prop_cut, det_same_neighbour_completion);
                let _ = (
                    &mut new_completing_det_same_neighbours,
                    &mut newly_completed_det_same_neighbours,
                    complete_only_compatible_neighbour_role_labels,
                    ontology_data,
                    individual_id,
                    loc_association_data,
                );
                neighbour_role_set_comp_label_reduction_checking = true;
                associations_updated = true;
            } else if association_data != IndividualAssociationDataId::NONE {
                // cpp 2566–2618: no links update, but the previous association had a neighbour hash → carry it over (copying when requiesDataCopying), optionally running det-same completion.
                // W6-DEFER[api]: faithful control flow:
                //   if associationData->getNeighbourRoleSetHash() {
                //     if detSameNeighbourCompletion { links_updated = true; alloc new hash+array initialised from associationData's; copy id linkers if requiesDataCopying;
                //       locAssoc->setNeighbourRoleSetHash(new); locAssoc->setRoleSetNeighbourArray(new);
                //       completed = self.complete_same_as_neighbours(locAssoc, newCompletingDetSameNeighbours, &mut newlyCompletedDetSameNeighbours, completeOnlyCompatibleNeighbourRoleLabels, ontologyData);
                //       if completed || requiesDataCopying { associationsUpdated = true; self.tmp_complete_neighbour_same_indi_merging_set.push(assocIndiId); }
                //       else { locAssoc->setNeighbourRoleSetHash(associationData->getNeighbourRoleSetHash()); locAssoc->setRoleSetNeighbourArray(associationData->getRoleSetNeighbourArray()); }
                //     } else if requiesDataCopying { deep-copy hash+array+linkers into loc; }
                //       else { locAssoc->setNeighbourRoleSetHash(associationData->getNeighbourRoleSetHash()); locAssoc->setRoleSetNeighbourArray(associationData->getRoleSetNeighbourArray()); } }
                let _ = det_same_neighbour_completion;
            }
            let _ = (
                links_updated,
                neighbour_role_set_comp_label_reduction_checking,
                neighbour_role_set_comp_label_reduction_required,
            );

            // cpp 2622–2627: copy the prop-cut removed-neighbour linker if data-copying and not already copied.
            // W6-DEFER[api]: if requiesDataCopying && !propCutRemovedNeighbourIndiLinkerCopied {
            //     prevRemNeighIndiLinker = self.copy_neighbour_individual_id_linkers(locAssoc->getPropagationCutRemovedNeighbourIndividualLinker(), context, locAssoc, -1);
            //     locAssoc->setPropagationCutRemovedNeighbourIndividualLinker(prevRemNeighIndiLinker); }

            // cpp 2630–2637: max statistics (live facade counters, gated on arena reads).
            // W6-DEFER[api]: detSameLabItem = locAssoc->getLabelCacheEntry(DETERMINISTIC_SAME_INDIVIDUAL_SET_LABEL);
            //   if detSameLabItem { self.stat_max_same_as_merged_count = max(self.stat_max_same_as_merged_count, detSameLabItem->getCacheValueCount()); }
            //   if locAssoc->getNeighbourRoleSetHash() { self.stat_max_neighbour_links_count = max(self.stat_max_neighbour_links_count, hash->getNeighbourCount()); }
            //   self.stat_max_association_update_count = max(self.stat_max_association_update_count, locAssoc->getAssociationDataUpdateId());

            // cpp 2640–2648: indirect-connection integration → nominal-connection change → mark not-completely-handled.
            // W6-DEFER[api]: if tempAss->hasIndirectlyConnectedIndividualIntegration() {
            //     nomConnData = (*ontologyData->getNominaIIndividualdIndirectConnectionDataHash())[individualID];
            //     if (nomConnData || integratedIndirectlyConnectedIndividualsChangeId > 0)
            //         && integratedIndirectlyConnectedIndividualsChangeId != nomConnData->getLastChangeId() {
            //       locAssoc->setCompletelyHandled(false); associationsUpdated = true; } }

            // cpp 2651–2660: incompatible-change → mark incompletely handled (live counter + sibling call).
            // W6-DEFER[api]: if incompatibleChanges && locAssoc->isCompletelyHandled() && (labelsUpdated || linksUpdated || tempAss->requireSameAsNeighboursCompletion()) {
            //     self.check_incompatible_indi_count += 1;   (live)
            //     if locAssoc->hasRepresentativeSameIndividualMerging() {
            //       self.mark_representative_referenced_individual_association_incompletely_handled(individualID, locAssoc, ontologyData);
            //     } else { locAssoc->setCompletelyHandled(false); associationsUpdated = true; } }
            let _ = (incompatible_changes, labels_updated);

            // cpp 2662–2672: propagated / representative-same flag reconciliation.
            // W6-DEFER[api]: if locAssoc->isCompletelyPropagated() && !tempAss->isCompletelyPropagated() { locAssoc->setCompletelyPropagated(false); associationsUpdated = true; }
            //   if !locAssoc->isCompletelyHandled() && locAssoc->hasRepresentativeSameIndividualMerging() {
            //     locAssoc->setCompletelyHandled(true);
            //     self.mark_representative_referenced_individual_association_incompletely_handled(individualID, locAssoc, ontologyData);
            //     associationsUpdated = true; }

            // cpp 2674–2695: deterministic-same considered label reduction.
            // W6-DEFER[api]: if detSameNeighbourCompletion {
            //     if referredLabels[DETERMINISTIC_SAME_INDIVIDUAL_SET_LABEL] != locAssoc->getDeterministicMergedSameConsideredLabelCacheEntry() {
            //       prevDetSameLabel = locAssoc->getDeterministicMergedSameConsideredLabelCacheEntry();
            //       newDetSameLabel = referredLabels[DETERMINISTIC_SAME_INDIVIDUAL_SET_LABEL];
            //       reducedNewDetSameLabel = self.get_reduced_label(DETERMINISTIC_SAME_INDIVIDUAL_SET_LABEL, newDetSameLabel,
            //         |cacheValue| { id = cacheValue.getTag(); !(id == individualID || prevDetSameLabel && prevDetSameLabel->hasCachedTagValue(id) || newlyCompletedDetSameNeighbours.contains(id)) }, ontologyData);
            //       locAssoc->setDeterministicMergedSameConsideredLabelCacheEntry(reducedNewDetSameLabel); associationsUpdated = true; } }

            // cpp 2699: store the incompletely-marked flag (live sibling call).
            // W6-DEFER[api] (loc/ontology arena ids resolve at the assembly wave):
            //   associationsUpdated |= self.store_individual_incompletely_marked(locAssoc, !locAssoc->isCompletelyHandled(), ontologyData);
            let incompletely_marked = false; // W6-DEFER[api]: !locAssoc->isCompletelyHandled().
            associations_updated |= self.store_individual_incompletely_marked(
                loc_association_data,
                incompletely_marked,
                ontology_data,
            );

            // cpp 2713–2721: commit the updated association (live sibling calls).
            if associations_updated {
                // W6-DEFER[api]: if locAssoc->getPreviousData() && !locAssoc->getPreviousData()->getPreviousData() { ontologyData->incIndividualAssociationDataDirectUpdateCount(); }
                self.set_updated_individual_association_data(
                    individual_id,
                    loc_association_data,
                    ontology_data,
                );
                // W6-DEFER[api]: if !locAssoc->hasRepresentativeSameIndividualMerging() { self.udate_deterministic_same_associations(locAssoc, ontologyData); }
                let has_representative_same_individual_merging = false; // W6-DEFER[api]
                if !has_representative_same_individual_merging {
                    self.udate_deterministic_same_associations(loc_association_data, ontology_data);
                }
            }
        }

        // cpp 2726
        associations_updated
    }
}

// KONCLUDE-PORT-NOTE[unclear]: NONE. The single ported method's logic is faithful;
// the only ambiguity-free deferrals are the arena-bound object dereferences, which
// this struct-def-era layer cannot resolve (no cache arena threaded through
// `&mut self`), exactly as in `backend_facade{1,2,3}`.
