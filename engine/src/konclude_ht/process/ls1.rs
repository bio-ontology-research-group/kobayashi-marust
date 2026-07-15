//! `process::ls1` (port unit **LS-1**) — the method bodies of
//! `CReapplyConceptLabelSet` (`Source/Reasoner/Kernel/Process/CReapplyConceptLabelSet.cpp`,
//! lines 34–528). The struct itself lives in `process::satellites`; this file is
//! exactly the `impl super::satellites::ReapplyConceptLabelSet { … }` block.
//!
//! CRITICAL — the copy-on-write (COW) heart is `init_concept_label_set` (C++
//! `initConceptLabelSet`, lines 65–103) and the `mAdditionalConceptDesDepMap`
//! fold inside every insert/get. It is ported BYTE-EXACT: the share-vs-rebuild
//! decision (`size <= 50` / `size*10 < additional.size`), the three states of the
//! additional map (null / owned-overflow / alias-into-another-label-set), and the
//! order of the state transitions are reproduced verbatim. They are NOT
//! simplified.
//!
//! ## How the COW is modelled (the one structural deviation)
//!
//! C++ `mAdditionalConceptDesDepMap` is a raw `CPROCESSMAP*` that is either
//! `nullptr`, owns a freshly-allocated overflow map, or **aliases another
//! `CReapplyConceptLabelSet`'s** `mConceptDesDepMap` / `mAdditionalConceptDesDepMap`
//! by bare pointer. The port keeps all three states first-class in
//! `AdditionalDesDepMapRef::{Null, Owned, Shared}` (defined in `satellites.rs`):
//!   * `Null`   == `nullptr`.
//!   * `Owned`  == the self-allocated overflow map (`allocateAndConstruct…`).
//!   * `Shared` == the bare-pointer alias, carrying the target `LabelSetId` + a
//!     `Main`/`Additional` slot discriminant (`LabelSetMapAlias`).
//! The translation of the C++ pointer-copy is exact (see `copy_additional_ref`):
//!   - `prev.additional == nullptr`  → self `Null`;
//!   - `prev.additional == Owned`    → self aliases prev's overflow map, i.e.
//!     `Shared{ prev_id, Additional }`;
//!   - `prev.additional == Shared(a)`→ self copies the same alias `a`.
//!
//! KONCLUDE-PORT-NOTE[ownership]: dereferencing a `Shared` alias needs the
//! label-set arena (to follow `LabelSetId` into another node's map). The legacy
//! standalone methods remain arena-free for existing callers, while the
//! `_in_context` LS-1 variants below follow shared aliases through
//! `ProcessContext`, matching the C++ raw-map pointer reads.

#![allow(dead_code)]

use std::collections::HashMap;

use super::super::model::ontology::OntologyArenas;
use super::super::model::substrate::Cint64;
use super::super::model::ConceptId;
use super::context::ProcessContext;
use super::reapply_sat::{LabelSetMapEntry, ReapplyConceptLabelSetIterator};
use super::satellites::{
    AdditionalDesDepMapRef, AdditionalMapSlot, ConceptDescriptorDependencyReapplyData,
    ConceptSetFlags, ConceptSetSignature, ConceptSetStructure, CondensedReapplyQueue,
    CoreConceptDescriptorId, LabelSetMapAlias, ReapplyConceptLabelSet,
};
use super::{ClashDescId, ConDescId, LabelSetId, TrackPointId};

// ===========================================================================
// Iterator return types
// ===========================================================================
// `CReapplyConceptLabelSetIterator` is now the REAL port (W3b, `reapply_sat`),
// imported above and built for real by `get_concept_label_set_iterator` below.
//
// KONCLUDE-PORT-NOTE[api]: `CCondensedReapplyQueueIterator` still has a local
// zero-size placeholder here because the `insertConcept*` out-iterator params and
// `completion/u36.rs` reference `ls1::CondensedReapplyQueueIterator`. The
// `getConceptReapplyIterator` getters return the REAL
// `super::reapply_sat::CondensedReapplyQueueIterator` (built below); the insert
// methods keep this placeholder until their un-defer wave reconciles them.

/// W2-DEFER[api] placeholder for `CCondensedReapplyQueueIterator` (insert-method
/// out-param only; the real iterator lives in `process::reapply_sat`).
pub struct CondensedReapplyQueueIterator;

impl ReapplyConceptLabelSet {
    // =======================================================================
    // === W2-DEFER[api] external-arena deref shims ==========================
    // =======================================================================
    // KONCLUDE-PORT-NOTE[api]: the C++ bodies dereference not-yet-ported arenas
    // (concept / concept-descriptor / flags / signature / structure / reapply
    // queue / clash). Each shim below is a faithful placeholder so the *local map
    // COW control flow* stays byte-exact; swap each for the real arena access when
    // those units land. The tag shims are kept MUTUALLY CONSISTENT (a concept tag
    // and the concept-descriptor's concept tag both reduce to the id's `.raw`), so
    // map keys still round-trip and the COW transitions are exercised correctly.

    /// W2-DEFER[api]: `CConcept::getConceptTag` (needs `Arena<Concept>`).
    #[inline]
    fn concept_tag(concept: ConceptId) -> Cint64 {
        concept.raw
    }
    /// W2-DEFER[api]: `CConceptDescriptor::getConceptTag` (descriptor → concept tag).
    #[inline]
    fn con_des_tag(con_des: ConDescId) -> Cint64 {
        con_des.raw
    }
    /// W2-DEFER[api]: `CConceptDescriptor::getConcept` (kept tag-consistent with the above).
    #[inline]
    fn con_des_concept(con_des: ConDescId) -> ConceptId {
        ConceptId::new(con_des.raw)
    }
    /// W2-DEFER[api]: `CConceptDescriptor::getNegation` / `isNegated` (descriptor arena).
    #[inline]
    fn con_des_negated(_con_des: ConDescId) -> bool {
        false
    }
    /// W2-DEFER[api]: `CConceptDescriptor::getDependencyTrackPoint` (descriptor arena).
    #[inline]
    fn con_des_dep_track_point(_con_des: ConDescId) -> TrackPointId {
        TrackPointId::NONE
    }
    #[inline]
    fn concept_tag_in_ontology(onto: &OntologyArenas, concept: ConceptId) -> Cint64 {
        onto.concept(concept).get_concept_tag()
    }
    #[inline]
    fn con_des_tag_in_context(
        ctx: &ProcessContext,
        onto: &OntologyArenas,
        con_des: ConDescId,
    ) -> Cint64 {
        ctx.con_desc(con_des).get_concept_tag(onto)
    }
    #[inline]
    fn con_des_concept_in_context(ctx: &ProcessContext, con_des: ConDescId) -> ConceptId {
        ctx.con_desc(con_des).get_concept()
    }
    #[inline]
    fn con_des_negated_in_context(ctx: &ProcessContext, con_des: ConDescId) -> bool {
        ctx.con_desc(con_des).is_negated()
    }
    #[inline]
    fn con_des_dep_track_point_in_context(
        ctx: &ProcessContext,
        con_des: ConDescId,
    ) -> TrackPointId {
        ctx.con_desc(con_des).get_dependency_track_point()
    }
    /// Port of `CCondensedReapplyQueue::isEmpty`.
    #[inline]
    fn queue_is_empty(q: &CondensedReapplyQueue) -> bool {
        q.is_empty()
    }

    // =======================================================================
    // === COW map helpers (the load-bearing part — exact for Null/Owned) ====
    // =======================================================================

    /// Deep-copy one `CConceptDescriptorDependencyReapplyData` (the map value).
    /// KONCLUDE-PORT-NOTE[ownership]: the value is not `Clone` (its embedded
    /// `CondensedReapplyQueue` placeholder is not yet a real type), so the copy is
    /// done field-by-field here. The descriptor id is `Copy`; the queue payload
    /// deep-copy is `// W2-DEFER[api]` (the placeholder carries no state yet).
    #[inline]
    fn clone_data(
        d: &ConceptDescriptorDependencyReapplyData,
    ) -> ConceptDescriptorDependencyReapplyData {
        ConceptDescriptorDependencyReapplyData {
            concept_descriptor: d.concept_descriptor,
            // u15: the queue is a value member sharing its chain head (the C++
            // `initReapplyQueue` share semantics); copy the head id.
            pos_neg_reapply_queue: d.pos_neg_reapply_queue,
        }
    }

    /// Value-copy a whole `CPROCESSMAP<cint64,…>` (`mConceptDesDepMap = other;`).
    fn clone_map(
        m: &HashMap<Cint64, ConceptDescriptorDependencyReapplyData>,
    ) -> HashMap<Cint64, ConceptDescriptorDependencyReapplyData> {
        m.iter().map(|(k, v)| (*k, Self::clone_data(v))).collect()
    }

    fn additional_alias_map_in_context<'a>(
        ctx: &'a ProcessContext,
        alias: LabelSetMapAlias,
    ) -> Option<&'a HashMap<Cint64, ConceptDescriptorDependencyReapplyData>> {
        let label_set = ctx.label_set(alias.label_set);
        match alias.which {
            AdditionalMapSlot::Main => Some(&label_set.concept_des_dep_map),
            AdditionalMapSlot::Additional => match &label_set.additional_concept_des_dep_map {
                AdditionalDesDepMapRef::Null => None,
                AdditionalDesDepMapRef::Owned(m) => Some(m),
                AdditionalDesDepMapRef::Shared(next_alias) => {
                    Self::additional_alias_map_in_context(ctx, *next_alias)
                }
            },
        }
    }

    /// `mAdditionalConceptDesDepMap != nullptr`.
    #[inline]
    fn additional_is_present(&self) -> bool {
        !matches!(
            self.additional_concept_des_dep_map,
            AdditionalDesDepMapRef::Null
        )
    }

    /// `mAdditionalConceptDesDepMap->size()` for legacy arena-free callers.
    /// Context-threaded callers use `additional_size_in_context` to follow
    /// `Shared` aliases through the label-set arena.
    #[inline]
    fn additional_size(&self) -> usize {
        match &self.additional_concept_des_dep_map {
            AdditionalDesDepMapRef::Null => 0,
            AdditionalDesDepMapRef::Owned(m) => m.len(),
            // Arena-free fallback; see `additional_size_in_context`.
            AdditionalDesDepMapRef::Shared(_) => 0,
        }
    }

    /// Context-threaded `mAdditionalConceptDesDepMap->size()`, following `Shared`
    /// aliases through the label-set arena like the C++ raw map pointer.
    #[inline]
    fn additional_size_in_context(&self, ctx: &ProcessContext) -> usize {
        match &self.additional_concept_des_dep_map {
            AdditionalDesDepMapRef::Null => 0,
            AdditionalDesDepMapRef::Owned(m) => m.len(),
            AdditionalDesDepMapRef::Shared(alias) => {
                Self::additional_alias_map_in_context(ctx, *alias).map_or(0, |m| m.len())
            }
        }
    }

    /// `mAdditionalConceptDesDepMap->tryGetValuePointer(conTag, …)` (read borrow).
    /// `Owned` → the entry; `Null`/`Shared` → `None` (`Shared` is `// W2-DEFER[api]`).
    #[inline]
    fn additional_get_ref(
        &self,
        con_tag: Cint64,
    ) -> Option<&ConceptDescriptorDependencyReapplyData> {
        match &self.additional_concept_des_dep_map {
            AdditionalDesDepMapRef::Null => None,
            AdditionalDesDepMapRef::Owned(m) => m.get(&con_tag),
            // W2-DEFER[api][unclear]: follow the alias into the referenced label set.
            AdditionalDesDepMapRef::Shared(_) => None,
        }
    }

    /// Context-threaded `mAdditionalConceptDesDepMap->tryGetValuePointer(conTag, ...)`.
    #[inline]
    fn additional_get_ref_in_context<'a>(
        &'a self,
        ctx: &'a ProcessContext,
        con_tag: Cint64,
    ) -> Option<&'a ConceptDescriptorDependencyReapplyData> {
        match &self.additional_concept_des_dep_map {
            AdditionalDesDepMapRef::Null => None,
            AdditionalDesDepMapRef::Owned(m) => m.get(&con_tag),
            AdditionalDesDepMapRef::Shared(alias) => {
                Self::additional_alias_map_in_context(ctx, *alias).and_then(|m| m.get(&con_tag))
            }
        }
    }

    /// `mAdditionalConceptDesDepMap->value(conTag)` cloned out of the borrow (so a
    /// `&mut` into `mConceptDesDepMap` can be taken afterwards) for legacy
    /// arena-free callers. Context-threaded callers use
    /// `additional_get_cloned_in_context`.
    #[inline]
    fn additional_get_cloned(
        &self,
        con_tag: Cint64,
    ) -> Option<ConceptDescriptorDependencyReapplyData> {
        match &self.additional_concept_des_dep_map {
            AdditionalDesDepMapRef::Null => None,
            AdditionalDesDepMapRef::Owned(m) => m.get(&con_tag).map(Self::clone_data),
            // Arena-free fallback; see `additional_get_cloned_in_context`.
            AdditionalDesDepMapRef::Shared(_) => None,
        }
    }

    /// Context-threaded `mAdditionalConceptDesDepMap->value(conTag)`, cloned out
    /// so callers can subsequently mutate the main map.
    #[inline]
    fn additional_get_cloned_in_context(
        &self,
        ctx: &ProcessContext,
        con_tag: Cint64,
    ) -> Option<ConceptDescriptorDependencyReapplyData> {
        match &self.additional_concept_des_dep_map {
            AdditionalDesDepMapRef::Null => None,
            AdditionalDesDepMapRef::Owned(m) => m.get(&con_tag).map(Self::clone_data),
            AdditionalDesDepMapRef::Shared(alias) => {
                Self::additional_alias_map_in_context(ctx, *alias)
                    .and_then(|m| m.get(&con_tag).map(Self::clone_data))
            }
        }
    }

    /// Translate `mAdditionalConceptDesDepMap = prev->mAdditionalConceptDesDepMap;`
    /// (the C++ bare-pointer copy) into the port's tri-state, exactly. See module
    /// doc for the three cases.
    #[inline]
    fn copy_additional_ref(
        prev_id: LabelSetId,
        prev: &ReapplyConceptLabelSet,
    ) -> AdditionalDesDepMapRef {
        match &prev.additional_concept_des_dep_map {
            AdditionalDesDepMapRef::Null => AdditionalDesDepMapRef::Null,
            // prev owns the overflow map; aliasing prev's pointer = pointing at
            // prev's `Additional` slot.
            AdditionalDesDepMapRef::Owned(_) => AdditionalDesDepMapRef::Shared(LabelSetMapAlias {
                label_set: prev_id,
                which: AdditionalMapSlot::Additional,
            }),
            // prev's additional already aliases someone else; copy the same alias.
            AdditionalDesDepMapRef::Shared(a) => AdditionalDesDepMapRef::Shared(*a),
        }
    }

    /// Clone the contents of the map `ls.mAdditionalConceptDesDepMap` points at
    /// (the `*newMap = *prev->mAdditionalConceptDesDepMap;` step) for legacy
    /// arena-free callers. Context-threaded callers use
    /// `clone_additional_contents_in_context`.
    fn clone_additional_contents(
        ls: &ReapplyConceptLabelSet,
    ) -> HashMap<Cint64, ConceptDescriptorDependencyReapplyData> {
        match &ls.additional_concept_des_dep_map {
            AdditionalDesDepMapRef::Null => HashMap::new(),
            AdditionalDesDepMapRef::Owned(m) => Self::clone_map(m),
            // Arena-free fallback; see `clone_additional_contents_in_context`.
            AdditionalDesDepMapRef::Shared(_) => HashMap::new(),
        }
    }

    fn clone_additional_contents_in_context(
        ctx: &ProcessContext,
        ls: &ReapplyConceptLabelSet,
    ) -> HashMap<Cint64, ConceptDescriptorDependencyReapplyData> {
        match &ls.additional_concept_des_dep_map {
            AdditionalDesDepMapRef::Null => HashMap::new(),
            AdditionalDesDepMapRef::Owned(m) => Self::clone_map(m),
            AdditionalDesDepMapRef::Shared(alias) => {
                Self::additional_alias_map_in_context(ctx, *alias)
                    .map_or_else(HashMap::new, Self::clone_map)
            }
        }
    }

    /// Port-facing helper for `mConceptSignature.addConceptSignature(conceptDescriptor)`.
    #[inline]
    fn add_concept_descriptor_signature(&mut self, concept_descriptor: ConDescId) {
        let concept = Self::con_des_concept(concept_descriptor);
        let con_tag = Self::con_des_tag(concept_descriptor);
        let negated = Self::con_des_negated(concept_descriptor);
        self.concept_signature
            .add_concept_signature(concept, con_tag, negated);
    }

    /// Context-threaded helper for
    /// `mConceptSignature.addConceptSignature(conceptDescriptor)`.
    #[inline]
    fn add_concept_descriptor_signature_in_context(
        &mut self,
        ctx: &ProcessContext,
        onto: &OntologyArenas,
        concept_descriptor: ConDescId,
    ) {
        let concept = Self::con_des_concept_in_context(ctx, concept_descriptor);
        let con_tag = Self::con_des_tag_in_context(ctx, onto, concept_descriptor);
        let negated = Self::con_des_negated_in_context(ctx, concept_descriptor);
        let concept_identity = onto.concept(concept) as *const _ as usize as Cint64;
        self.concept_signature.add_concept_signature_with_identity(
            con_tag,
            negated,
            concept_identity,
        );
    }

    // =======================================================================
    // === ported methods (C++ order) =======================================
    // =======================================================================

    /// Port of `getConceptFlags`.
    pub fn get_concept_flags(&mut self) -> &mut ConceptSetFlags {
        &mut self.concept_flags
    }

    /// Port of `getConceptSignature`.
    pub fn get_concept_signature(&mut self) -> &mut ConceptSetSignature {
        &mut self.concept_signature
    }

    /// Port of `getConceptStructure`.
    pub fn get_concept_structure(&mut self) -> &mut ConceptSetStructure {
        &mut self.concept_structure
    }

    /// Port of `initConceptLabelSet` — **the COW heart** (C++ lines 65–103).
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: C++ takes `CReapplyConceptLabelSet* prev`. The
    /// port takes `Option<(LabelSetId, &ReapplyConceptLabelSet)>`: `None` == the
    /// `prev == nullptr` branch; the id is needed to build a `Shared` alias that
    /// points back at `prev`.
    pub fn init_concept_label_set(
        &mut self,
        prev: Option<(LabelSetId, &ReapplyConceptLabelSet)>,
    ) -> &mut Self {
        if let Some((prev_id, prev)) = prev {
            self.concept_des_linker = prev.concept_des_linker;
            self.prev_concept_des_linker = self.concept_des_linker;
            self.concept_count = prev.concept_count;
            // C++ line 70 — preserve the `&&`-binds-tighter-than-`||` precedence:
            //   (!prev.add && prev.main.size() <= 50)
            //   || (prev.add && prev.main.size()*10 < prev.add->size())
            let prev_add_present = prev.additional_is_present();
            let prev_main_size = prev.concept_des_dep_map.len();
            let share = (!prev_add_present && prev_main_size <= 50)
                || (prev_add_present && prev_main_size * 10 < prev.additional_size());
            if share {
                // share branch (lines 71–72): value-copy prev's main map + copy the
                // additional-map pointer.
                self.concept_des_dep_map = Self::clone_map(&prev.concept_des_dep_map);
                self.additional_concept_des_dep_map = Self::copy_additional_ref(prev_id, prev);
            } else {
                // rebuild branch (lines 74–85).
                self.concept_des_dep_map.clear();
                if prev_add_present {
                    // allocate a fresh overflow map, copy prev's additional into it,
                    // then merge every prev main entry on top (lines 76–82).
                    let mut new_map = Self::clone_additional_contents(prev);
                    for (con_tag, con_data) in prev.concept_des_dep_map.iter() {
                        new_map.insert(*con_tag, Self::clone_data(con_data));
                    }
                    self.additional_concept_des_dep_map = AdditionalDesDepMapRef::Owned(new_map);
                } else {
                    // alias prev's MAIN map (line 84:
                    // `mAdditionalConceptDesDepMap = &prev->mConceptDesDepMap;`).
                    self.additional_concept_des_dep_map =
                        AdditionalDesDepMapRef::Shared(LabelSetMapAlias {
                            label_set: prev_id,
                            which: AdditionalMapSlot::Main,
                        });
                }
            }
            // lines 87–90.
            // W2-DEFER[api]: `mConceptFlags`/`mConceptStructure` are fieldless
            // placeholders; copy is trivial today and lands fully with the types.
            self.concept_flags = ConceptSetFlags::default();
            self.concept_signature = prev.concept_signature;
            self.core_con_des_linker = prev.core_con_des_linker;
            self.concept_structure = ConceptSetStructure::default();
        } else {
            // prev == nullptr branch (lines 92–100).
            self.concept_des_dep_map.clear();
            self.additional_concept_des_dep_map = AdditionalDesDepMapRef::Null;
            self.concept_des_linker = ConDescId::NONE;
            self.prev_concept_des_linker = ConDescId::NONE;
            self.core_con_des_linker = CoreConceptDescriptorId::NONE;
            self.concept_count = 0;
            // W2-DEFER[api]: mConceptFlags.reset()/mConceptSignature.reset()/mConceptStructure.reset().
            self.concept_flags = ConceptSetFlags::default();
            self.concept_signature = ConceptSetSignature::default();
            self.concept_structure = ConceptSetStructure::default();
        }
        self
    }

    /// Context-threaded `initConceptLabelSet` variant for callers that can supply
    /// the label-set arena, allowing the share/rebuild decision and the rebuild
    /// copy to read through `Shared` additional-map aliases.
    pub fn init_concept_label_set_in_context(
        &mut self,
        ctx: &ProcessContext,
        prev: Option<(LabelSetId, &ReapplyConceptLabelSet)>,
    ) -> &mut Self {
        if let Some((prev_id, prev)) = prev {
            self.concept_des_linker = prev.concept_des_linker;
            self.prev_concept_des_linker = self.concept_des_linker;
            self.concept_count = prev.concept_count;
            let prev_add_present = prev.additional_is_present();
            let prev_main_size = prev.concept_des_dep_map.len();
            let share = (!prev_add_present && prev_main_size <= 50)
                || (prev_add_present && prev_main_size * 10 < prev.additional_size_in_context(ctx));
            if share {
                self.concept_des_dep_map = Self::clone_map(&prev.concept_des_dep_map);
                self.additional_concept_des_dep_map = Self::copy_additional_ref(prev_id, prev);
            } else {
                self.concept_des_dep_map.clear();
                if prev_add_present {
                    let mut new_map = Self::clone_additional_contents_in_context(ctx, prev);
                    for (con_tag, con_data) in prev.concept_des_dep_map.iter() {
                        new_map.insert(*con_tag, Self::clone_data(con_data));
                    }
                    self.additional_concept_des_dep_map = AdditionalDesDepMapRef::Owned(new_map);
                } else {
                    self.additional_concept_des_dep_map =
                        AdditionalDesDepMapRef::Shared(LabelSetMapAlias {
                            label_set: prev_id,
                            which: AdditionalMapSlot::Main,
                        });
                }
            }
            self.concept_flags = ConceptSetFlags::default();
            self.concept_signature = prev.concept_signature;
            self.core_con_des_linker = prev.core_con_des_linker;
            self.concept_structure = ConceptSetStructure::default();
        } else {
            self.init_concept_label_set(None);
        }
        self
    }

    /// Port of `addCoreConceptDescriptor`.
    pub fn add_core_concept_descriptor(
        &mut self,
        core_con_des: CoreConceptDescriptorId,
    ) -> &mut Self {
        self.core_con_des_linker = core_con_des;
        self
    }

    /// Port of `hasConceptDescriptor`.
    pub fn has_concept_descriptor(&self, concept_descriptor: ConDescId) -> bool {
        // W2-DEFER[api]: conceptDescriptor->getConcept()/getNegation() (descriptor arena).
        self.has_concept(
            Self::con_des_concept(concept_descriptor),
            Self::con_des_negated(concept_descriptor),
        )
    }

    /// Context-threaded `hasConceptDescriptor` using the descriptor and concept
    /// arenas instead of the legacy id-as-tag descriptor shims.
    pub fn has_concept_descriptor_in_context(
        &self,
        ctx: &ProcessContext,
        onto: &OntologyArenas,
        concept_descriptor: ConDescId,
    ) -> bool {
        self.has_concept_in_context(
            ctx,
            onto,
            Self::con_des_concept_in_context(ctx, concept_descriptor),
            Self::con_des_negated_in_context(ctx, concept_descriptor),
        )
    }

    /// Port of `containsConceptDescriptor`.
    pub fn contains_concept_descriptor(&self, concept_descriptor: ConDescId) -> bool {
        self.has_concept_descriptor(concept_descriptor)
    }

    /// Context-threaded `containsConceptDescriptor`.
    pub fn contains_concept_descriptor_in_context(
        &self,
        ctx: &ProcessContext,
        onto: &OntologyArenas,
        concept_descriptor: ConDescId,
    ) -> bool {
        self.has_concept_descriptor_in_context(ctx, onto, concept_descriptor)
    }

    /// Port of `hasConcept(CConcept*, bool negated)`.
    pub fn has_concept(&self, concept: ConceptId, negated: bool) -> bool {
        // W2-DEFER[api]: mConceptFlags.containsConceptFlags(concept, negated) — the
        // flag filter is a soundness-neutral pruning hint; stubbed to "maybe", which
        // keeps the full map lookup (no false prune).
        // if (!contains_concept_flags) return false;
        let con_tag = Self::concept_tag(concept);
        let mut con_des_dep_data = self.concept_des_dep_map.get(&con_tag);
        let mut is_contained = con_des_dep_data.is_some();
        if con_des_dep_data.is_none() && self.additional_is_present() {
            con_des_dep_data = self.additional_get_ref(con_tag);
            is_contained = con_des_dep_data.is_some();
        }
        is_contained
            && con_des_dep_data.map_or(false, |d| {
                d.concept_descriptor.is_some()
                    && Self::con_des_negated(d.concept_descriptor) == negated
            })
    }

    /// Context-threaded `hasConcept(CConcept*, bool negated)`.
    pub fn has_concept_in_context(
        &self,
        ctx: &ProcessContext,
        onto: &OntologyArenas,
        concept: ConceptId,
        negated: bool,
    ) -> bool {
        let con_tag = Self::concept_tag_in_ontology(onto, concept);
        let mut con_des_dep_data = self.concept_des_dep_map.get(&con_tag);
        let mut is_contained = con_des_dep_data.is_some();
        if con_des_dep_data.is_none() && self.additional_is_present() {
            con_des_dep_data = self.additional_get_ref_in_context(ctx, con_tag);
            is_contained = con_des_dep_data.is_some();
        }
        is_contained
            && con_des_dep_data.map_or(false, |d| {
                d.concept_descriptor.is_some()
                    && Self::con_des_negated_in_context(ctx, d.concept_descriptor) == negated
            })
    }

    /// Port of `hasConcept(CConcept*, bool* containsNegated)`.
    pub fn has_concept_get_negated(
        &self,
        concept: ConceptId,
        contains_negated: Option<&mut bool>,
    ) -> bool {
        // W2-DEFER[api]: mConceptFlags.containsConceptFlags(concept).
        let con_tag = Self::concept_tag(concept);
        let mut con_des_dep_data = self.concept_des_dep_map.get(&con_tag);
        let mut is_contained = con_des_dep_data.is_some();
        if con_des_dep_data.is_none() && self.additional_is_present() {
            con_des_dep_data = self.additional_get_ref(con_tag);
            is_contained = con_des_dep_data.is_some();
        }
        if is_contained {
            if let Some(out) = contains_negated {
                *out = con_des_dep_data.map_or(false, |d| {
                    d.concept_descriptor.is_some() && Self::con_des_negated(d.concept_descriptor)
                });
            }
        }
        is_contained && con_des_dep_data.map_or(false, |d| d.concept_descriptor.is_some())
    }

    /// Context-threaded `hasConcept(CConcept*, bool* containsNegated)`.
    pub fn has_concept_get_negated_in_context(
        &self,
        ctx: &ProcessContext,
        onto: &OntologyArenas,
        concept: ConceptId,
        contains_negated: Option<&mut bool>,
    ) -> bool {
        let con_tag = Self::concept_tag_in_ontology(onto, concept);
        let mut con_des_dep_data = self.concept_des_dep_map.get(&con_tag);
        let mut is_contained = con_des_dep_data.is_some();
        if con_des_dep_data.is_none() && self.additional_is_present() {
            con_des_dep_data = self.additional_get_ref_in_context(ctx, con_tag);
            is_contained = con_des_dep_data.is_some();
        }
        if is_contained {
            if let Some(out) = contains_negated {
                *out = con_des_dep_data.map_or(false, |d| {
                    d.concept_descriptor.is_some()
                        && Self::con_des_negated_in_context(ctx, d.concept_descriptor)
                });
            }
        }
        is_contained && con_des_dep_data.map_or(false, |d| d.concept_descriptor.is_some())
    }

    /// Port of `containsConcept(CConcept*, bool* containsNegated)`.
    pub fn contains_concept_get_negated(
        &self,
        concept: ConceptId,
        contains_negated: Option<&mut bool>,
    ) -> bool {
        self.has_concept_get_negated(concept, contains_negated)
    }

    /// Port of `containsConcept(CConcept*, bool negated)`.
    pub fn contains_concept(&self, concept: ConceptId, negated: bool) -> bool {
        self.has_concept(concept, negated)
    }

    /// Context-threaded `containsConcept(CConcept*, bool negated)`.
    pub fn contains_concept_in_context(
        &self,
        ctx: &ProcessContext,
        onto: &OntologyArenas,
        concept: ConceptId,
        negated: bool,
    ) -> bool {
        self.has_concept_in_context(ctx, onto, concept, negated)
    }

    /// Port of `getConceptDescriptor(CConcept*, CConceptDescriptor*&, CDependencyTrackPoint*&)`.
    pub fn get_concept_descriptor(
        &self,
        concept: ConceptId,
        con_des: &mut ConDescId,
        dep_track_point: &mut TrackPointId,
    ) -> bool {
        self.get_concept_descriptor_by_tag(Self::concept_tag(concept), con_des, dep_track_point)
    }

    /// Context-threaded `getConceptDescriptor(CConcept*, ...)`.
    pub fn get_concept_descriptor_in_context(
        &self,
        ctx: &ProcessContext,
        onto: &OntologyArenas,
        concept: ConceptId,
        con_des: &mut ConDescId,
        dep_track_point: &mut TrackPointId,
    ) -> bool {
        self.get_concept_descriptor_by_tag_in_context(
            ctx,
            Self::concept_tag_in_ontology(onto, concept),
            con_des,
            dep_track_point,
        )
    }

    /// Port of `getConceptDescriptor(cint64 conTag, CConceptDescriptor*&, CDependencyTrackPoint*&)`.
    pub fn get_concept_descriptor_by_tag(
        &self,
        con_tag: Cint64,
        con_des: &mut ConDescId,
        dep_track_point: &mut TrackPointId,
    ) -> bool {
        let mut con_des_dep_data = self.concept_des_dep_map.get(&con_tag);
        let mut contained = con_des_dep_data.is_some();
        if con_des_dep_data.is_none() && self.additional_is_present() {
            con_des_dep_data = self.additional_get_ref(con_tag);
            contained = con_des_dep_data.is_some();
        }
        if contained {
            let data = con_des_dep_data.unwrap();
            *con_des = data.concept_descriptor;
            if con_des.is_some() {
                *dep_track_point = Self::con_des_dep_track_point(*con_des);
            } else {
                *dep_track_point = TrackPointId::NONE;
            }
            contained &= con_des.is_some();
        }
        contained
    }

    /// Context-threaded `getConceptDescriptor(cint64 conTag, ...)`.
    pub fn get_concept_descriptor_by_tag_in_context(
        &self,
        ctx: &ProcessContext,
        con_tag: Cint64,
        con_des: &mut ConDescId,
        dep_track_point: &mut TrackPointId,
    ) -> bool {
        let mut con_des_dep_data = self.concept_des_dep_map.get(&con_tag);
        let mut contained = con_des_dep_data.is_some();
        if con_des_dep_data.is_none() && self.additional_is_present() {
            con_des_dep_data = self.additional_get_ref_in_context(ctx, con_tag);
            contained = con_des_dep_data.is_some();
        }
        if contained {
            let data = con_des_dep_data.unwrap();
            *con_des = data.concept_descriptor;
            if con_des.is_some() {
                *dep_track_point = Self::con_des_dep_track_point_in_context(ctx, *con_des);
            } else {
                *dep_track_point = TrackPointId::NONE;
            }
            contained &= con_des.is_some();
        }
        contained
    }

    /// Port of `insertConceptIgnoreClash`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: `depTrackPoint` is unused in the C++ body (kept for
    /// signature fidelity); `reapplyQueueIt` is an out-iterator (placeholder).
    pub fn insert_concept_ignore_clash(
        &mut self,
        concept_descriptor: ConDescId,
        _dep_track_point: TrackPointId,
        reapply_queue_it: Option<&mut CondensedReapplyQueueIterator>,
    ) -> bool {
        let con_tag = Self::con_des_tag(concept_descriptor);
        let add_present = self.additional_is_present();
        // `mConceptDesDepMap[conTag]` (insert default if absent). Pull the additional
        // value out *before* the &mut borrow to avoid aliasing.
        let add_opt = if add_present {
            self.additional_get_cloned(con_tag)
        } else {
            None
        };
        let con_des_dep_data = self
            .concept_des_dep_map
            .entry(con_tag)
            .or_insert_with(ConceptDescriptorDependencyReapplyData::default);
        if add_present
            && con_des_dep_data.concept_descriptor.is_none()
            && Self::queue_is_empty(&con_des_dep_data.pos_neg_reapply_queue)
        {
            if let Some(add) = add_opt {
                *con_des_dep_data = add;
            }
        }
        con_des_dep_data.concept_descriptor = concept_descriptor;
        self.concept_count += 1;
        self.add_concept_descriptor_signature(concept_descriptor);
        // W2-DEFER[api]: mConceptFlags.addConceptFlags /
        //               mConceptStructure.addedConcept(conceptDescriptor).
        // W2-DEFER[api]: mConceptDesLinker = conceptDescriptor->append(mConceptDesLinker).
        self.concept_des_linker = concept_descriptor;
        if let Some(it) = reapply_queue_it {
            // W2-DEFER[api]: pos_neg_reapply_queue.getIterator(conceptDescriptor->isNegated(), true).
            *it = CondensedReapplyQueueIterator;
        }
        true
    }

    /// Context-threaded `insertConceptIgnoreClash`.
    pub fn insert_concept_ignore_clash_in_context(
        &mut self,
        ctx: &ProcessContext,
        onto: &OntologyArenas,
        concept_descriptor: ConDescId,
        _dep_track_point: TrackPointId,
        reapply_queue_it: Option<&mut CondensedReapplyQueueIterator>,
    ) -> bool {
        let con_tag = Self::con_des_tag_in_context(ctx, onto, concept_descriptor);
        let add_present = self.additional_is_present();
        let add_opt = if add_present {
            self.additional_get_cloned_in_context(ctx, con_tag)
        } else {
            None
        };
        let con_des_dep_data = self
            .concept_des_dep_map
            .entry(con_tag)
            .or_insert_with(ConceptDescriptorDependencyReapplyData::default);
        if add_present
            && con_des_dep_data.concept_descriptor.is_none()
            && Self::queue_is_empty(&con_des_dep_data.pos_neg_reapply_queue)
        {
            if let Some(add) = add_opt {
                *con_des_dep_data = add;
            }
        }
        con_des_dep_data.concept_descriptor = concept_descriptor;
        self.concept_count += 1;
        self.add_concept_descriptor_signature_in_context(ctx, onto, concept_descriptor);
        self.concept_des_linker = concept_descriptor;
        if let Some(it) = reapply_queue_it {
            *it = CondensedReapplyQueueIterator;
        }
        true
    }

    /// Port of `insertConceptGetClash`.
    pub fn insert_concept_get_clash(
        &mut self,
        concept_descriptor: ConDescId,
        _dep_track_point: TrackPointId,
        reapply_queue_it: Option<&mut CondensedReapplyQueueIterator>,
        clashed_con_des: Option<&mut ConDescId>,
        clashed_dep_track_point: Option<&mut TrackPointId>,
    ) -> bool {
        let con_tag = Self::con_des_tag(concept_descriptor);
        let add_present = self.additional_is_present();
        let add_opt = if add_present {
            self.additional_get_cloned(con_tag)
        } else {
            None
        };
        // tryInsert(conTag, data(conceptDescriptor), &containsAlready, &containedConDesDepData).
        let existed = self.concept_des_dep_map.contains_key(&con_tag);
        let contained_con_des_dep_data =
            self.concept_des_dep_map.entry(con_tag).or_insert_with(|| {
                ConceptDescriptorDependencyReapplyData {
                    concept_descriptor,
                    pos_neg_reapply_queue: CondensedReapplyQueue::new(),
                }
            });
        let mut contains_already = existed;
        // C++ tracks containFromAdditionMap but never reads it afterwards.
        let mut _contain_from_addition_map = false;
        if !contains_already && add_present {
            if let Some(add) = add_opt {
                if add.concept_descriptor.is_some()
                    || !Self::queue_is_empty(&add.pos_neg_reapply_queue)
                {
                    *contained_con_des_dep_data = add;
                    contains_already = true;
                    _contain_from_addition_map = true;
                }
            }
        }
        if contained_con_des_dep_data.concept_descriptor.is_none() {
            contained_con_des_dep_data.concept_descriptor = concept_descriptor;
            contains_already = false;
        }
        if contains_already {
            let contains_con_des = contained_con_des_dep_data.concept_descriptor;
            if Self::con_des_negated(contains_con_des) != Self::con_des_negated(concept_descriptor)
            {
                if let Some(out) = clashed_con_des {
                    *out = contains_con_des;
                }
                if let Some(out) = clashed_dep_track_point {
                    *out = Self::con_des_dep_track_point(contains_con_des);
                }
            }
            true
        } else {
            self.concept_count += 1;
            self.add_concept_descriptor_signature(concept_descriptor);
            // W2-DEFER[api]: mConceptFlags.addConceptFlags /
            //               mConceptStructure.addedConcept(conceptDescriptor).
            // W2-DEFER[api]: mConceptDesLinker = conceptDescriptor->append(mConceptDesLinker).
            self.concept_des_linker = concept_descriptor;
            if let Some(it) = reapply_queue_it {
                // W2-DEFER[api]: pos_neg_reapply_queue.getIterator(conceptDescriptor->isNegated(), true).
                *it = CondensedReapplyQueueIterator;
            }
            false
        }
    }

    /// Context-threaded `insertConceptGetClash`.
    pub fn insert_concept_get_clash_in_context(
        &mut self,
        ctx: &ProcessContext,
        onto: &OntologyArenas,
        concept_descriptor: ConDescId,
        _dep_track_point: TrackPointId,
        reapply_queue_it: Option<&mut CondensedReapplyQueueIterator>,
        clashed_con_des: Option<&mut ConDescId>,
        clashed_dep_track_point: Option<&mut TrackPointId>,
    ) -> bool {
        let con_tag = Self::con_des_tag_in_context(ctx, onto, concept_descriptor);
        let add_present = self.additional_is_present();
        let add_opt = if add_present {
            self.additional_get_cloned_in_context(ctx, con_tag)
        } else {
            None
        };
        let existed = self.concept_des_dep_map.contains_key(&con_tag);
        let contained_con_des_dep_data =
            self.concept_des_dep_map.entry(con_tag).or_insert_with(|| {
                ConceptDescriptorDependencyReapplyData {
                    concept_descriptor,
                    pos_neg_reapply_queue: CondensedReapplyQueue::new(),
                }
            });
        let mut contains_already = existed;
        let mut _contain_from_addition_map = false;
        if !contains_already && add_present {
            if let Some(add) = add_opt {
                if add.concept_descriptor.is_some()
                    || !Self::queue_is_empty(&add.pos_neg_reapply_queue)
                {
                    *contained_con_des_dep_data = add;
                    contains_already = true;
                    _contain_from_addition_map = true;
                }
            }
        }
        if contained_con_des_dep_data.concept_descriptor.is_none() {
            contained_con_des_dep_data.concept_descriptor = concept_descriptor;
            contains_already = false;
        }
        if contains_already {
            let contains_con_des = contained_con_des_dep_data.concept_descriptor;
            if Self::con_des_negated_in_context(ctx, contains_con_des)
                != Self::con_des_negated_in_context(ctx, concept_descriptor)
            {
                if let Some(out) = clashed_con_des {
                    *out = contains_con_des;
                }
                if let Some(out) = clashed_dep_track_point {
                    *out = Self::con_des_dep_track_point_in_context(ctx, contains_con_des);
                }
            }
            true
        } else {
            self.concept_count += 1;
            self.add_concept_descriptor_signature_in_context(ctx, onto, concept_descriptor);
            self.concept_des_linker = concept_descriptor;
            if let Some(it) = reapply_queue_it {
                *it = CondensedReapplyQueueIterator;
            }
            false
        }
    }

    /// W5 un-defer of `insertConceptGetClash` with the descriptor arena resolved.
    ///
    /// The plain `insert_concept_get_clash` keys the map by the local `con_des_tag`
    /// shim (the descriptor id) and reads `con_des_negated` as a constant `false`,
    /// because `CReapplyConceptLabelSet` cannot resolve a `ConDescId` against the
    /// per-test descriptor arena from `&mut self`. For the W5 behavioural milestone
    /// the caller (`insert_concepts_to_individual_concept_set`, which DOES hold the
    /// context) resolves the new descriptor's real concept tag + negation and passes
    /// a `desc_negated` resolver for the EXISTING stored descriptor, so the clash
    /// branch (`getNegation() != getNegation()`) becomes live and faithful. The
    /// map-keying-by-concept-tag and the polarity compare are exactly the C++
    /// `insertConceptGetClash` (lines 200–280); only the deref source moved from the
    /// W2-DEFER shims to the threaded resolvers.
    pub fn insert_concept_get_clash_resolved(
        &mut self,
        concept_descriptor: ConDescId,
        concept: ConceptId,
        con_tag: Cint64,
        negated: bool,
        concept_identity: Cint64,
        desc_negated: &dyn Fn(ConDescId) -> bool,
        clashed_con_des: Option<&mut ConDescId>,
        clashed_dep_track_point: Option<&mut TrackPointId>,
    ) -> bool {
        let add_present = self.additional_is_present();
        let add_opt = if add_present {
            self.additional_get_cloned(con_tag)
        } else {
            None
        };
        let existed = self.concept_des_dep_map.contains_key(&con_tag);
        let contained_con_des_dep_data =
            self.concept_des_dep_map.entry(con_tag).or_insert_with(|| {
                ConceptDescriptorDependencyReapplyData {
                    concept_descriptor,
                    pos_neg_reapply_queue: CondensedReapplyQueue::new(),
                }
            });
        let mut contains_already = existed;
        if !contains_already && add_present {
            if let Some(add) = add_opt {
                if add.concept_descriptor.is_some()
                    || !Self::queue_is_empty(&add.pos_neg_reapply_queue)
                {
                    *contained_con_des_dep_data = add;
                    contains_already = true;
                }
            }
        }
        if contained_con_des_dep_data.concept_descriptor.is_none() {
            contained_con_des_dep_data.concept_descriptor = concept_descriptor;
            contains_already = false;
        }
        if contains_already {
            let contains_con_des = contained_con_des_dep_data.concept_descriptor;
            // CConceptDescriptor::getNegation() of the stored vs the new descriptor.
            if desc_negated(contains_con_des) != negated {
                if let Some(out) = clashed_con_des {
                    *out = contains_con_des;
                }
                if let Some(out) = clashed_dep_track_point {
                    *out = Self::con_des_dep_track_point(contains_con_des);
                }
            }
            true
        } else {
            self.concept_count += 1;
            self.concept_signature.add_concept_signature_with_identity(
                con_tag,
                negated,
                concept_identity,
            );
            // W2-DEFER[api]: mConceptFlags.addConceptFlags / mConceptStructure.addedConcept.
            self.concept_des_linker = concept_descriptor;
            false
        }
    }

    /// Port of `insertConceptReturnClash` → `CClashedConceptDescriptor*`
    /// (`ClashDescId::NONE` == `nullptr`).
    ///
    /// KONCLUDE-PORT-NOTE[api]: the clash record is allocated + initialised +
    /// chained (`CObjectAllocator<CClashedConceptDescriptor>` …, lines 282–287) in
    /// the clash arena, which is not ported. The clash *detection* branch is
    /// preserved exactly; the allocation is `// W2-DEFER[api]` and returns
    /// `ClashDescId::NONE` for now.
    pub fn insert_concept_return_clash(
        &mut self,
        concept_descriptor: ConDescId,
        _dep_track_point: TrackPointId,
        has_contained: Option<&mut bool>,
        reapply_queue_it: Option<&mut CondensedReapplyQueueIterator>,
    ) -> ClashDescId {
        let con_tag = Self::con_des_tag(concept_descriptor);
        let add_present = self.additional_is_present();
        let add_opt = if add_present {
            self.additional_get_cloned(con_tag)
        } else {
            None
        };
        let existed = self.concept_des_dep_map.contains_key(&con_tag);
        let contained_con_des_dep_data =
            self.concept_des_dep_map.entry(con_tag).or_insert_with(|| {
                ConceptDescriptorDependencyReapplyData {
                    concept_descriptor,
                    pos_neg_reapply_queue: CondensedReapplyQueue::new(),
                }
            });
        let mut contains_already = existed;
        if !contains_already && add_present {
            if let Some(add) = add_opt {
                if add.concept_descriptor.is_some()
                    || !Self::queue_is_empty(&add.pos_neg_reapply_queue)
                {
                    *contained_con_des_dep_data = add;
                    contains_already = true;
                }
            }
        }
        if contained_con_des_dep_data.concept_descriptor.is_none() {
            contained_con_des_dep_data.concept_descriptor = concept_descriptor;
            contains_already = false;
        }
        if contains_already {
            if let Some(out) = has_contained {
                *out = true;
            }
            let contains_con_des = contained_con_des_dep_data.concept_descriptor;
            if Self::con_des_negated(contains_con_des) != Self::con_des_negated(concept_descriptor)
            {
                let _contains_dep_track_point = Self::con_des_dep_track_point(contains_con_des);
                // W2-DEFER[api]: allocate clashDes1/clashDes2, init from
                // (conceptDescriptor, depTrackPoint) + (containsConDes, containsDepTrackPoint),
                // chain clashDes1->append(clashDes2), return clashDes1.
                return ClashDescId::NONE;
            }
        } else {
            if let Some(out) = has_contained {
                *out = false;
            }
            self.concept_count += 1;
            self.add_concept_descriptor_signature(concept_descriptor);
            // W2-DEFER[api]: mConceptFlags.addConceptFlags /
            //               mConceptStructure.addedConcept(conceptDescriptor).
            // W2-DEFER[api]: mConceptDesLinker = conceptDescriptor->append(mConceptDesLinker).
            self.concept_des_linker = concept_descriptor;
            if let Some(it) = reapply_queue_it {
                // W2-DEFER[api]: pos_neg_reapply_queue.getIterator(conceptDescriptor->isNegated(), true).
                *it = CondensedReapplyQueueIterator;
            }
        }
        ClashDescId::NONE
    }

    /// Context-threaded `insertConceptReturnClash`.
    pub fn insert_concept_return_clash_in_context(
        &mut self,
        ctx: &ProcessContext,
        onto: &OntologyArenas,
        concept_descriptor: ConDescId,
        _dep_track_point: TrackPointId,
        has_contained: Option<&mut bool>,
        reapply_queue_it: Option<&mut CondensedReapplyQueueIterator>,
    ) -> ClashDescId {
        let con_tag = Self::con_des_tag_in_context(ctx, onto, concept_descriptor);
        let add_present = self.additional_is_present();
        let add_opt = if add_present {
            self.additional_get_cloned_in_context(ctx, con_tag)
        } else {
            None
        };
        let existed = self.concept_des_dep_map.contains_key(&con_tag);
        let contained_con_des_dep_data =
            self.concept_des_dep_map.entry(con_tag).or_insert_with(|| {
                ConceptDescriptorDependencyReapplyData {
                    concept_descriptor,
                    pos_neg_reapply_queue: CondensedReapplyQueue::new(),
                }
            });
        let mut contains_already = existed;
        if !contains_already && add_present {
            if let Some(add) = add_opt {
                if add.concept_descriptor.is_some()
                    || !Self::queue_is_empty(&add.pos_neg_reapply_queue)
                {
                    *contained_con_des_dep_data = add;
                    contains_already = true;
                }
            }
        }
        if contained_con_des_dep_data.concept_descriptor.is_none() {
            contained_con_des_dep_data.concept_descriptor = concept_descriptor;
            contains_already = false;
        }
        if contains_already {
            if let Some(out) = has_contained {
                *out = true;
            }
            let contains_con_des = contained_con_des_dep_data.concept_descriptor;
            if Self::con_des_negated_in_context(ctx, contains_con_des)
                != Self::con_des_negated_in_context(ctx, concept_descriptor)
            {
                let _contains_dep_track_point =
                    Self::con_des_dep_track_point_in_context(ctx, contains_con_des);
                return ClashDescId::NONE;
            }
        } else {
            if let Some(out) = has_contained {
                *out = false;
            }
            self.concept_count += 1;
            self.add_concept_descriptor_signature_in_context(ctx, onto, concept_descriptor);
            self.concept_des_linker = concept_descriptor;
            if let Some(it) = reapply_queue_it {
                *it = CondensedReapplyQueueIterator;
            }
        }
        ClashDescId::NONE
    }

    /// Port of `insertConceptThrowClashReturnContained`.
    ///
    /// KONCLUDE-PORT-NOTE[exceptions]: the C++ `throw clash;` is modelled as
    /// `Err(clash)`; `Ok(contained)` is the non-clash return. (Clash allocation is
    /// itself `// W2-DEFER[api]` in `insert_concept_return_clash`, so `Err` does not
    /// fire yet.)
    pub fn insert_concept_throw_clash_return_contained(
        &mut self,
        concept_descriptor: ConDescId,
        dep_track_point: TrackPointId,
        reapply_queue_it: Option<&mut CondensedReapplyQueueIterator>,
    ) -> Result<bool, ClashDescId> {
        let mut contained = false;
        let clash = self.insert_concept_return_clash(
            concept_descriptor,
            dep_track_point,
            Some(&mut contained),
            reapply_queue_it,
        );
        if clash.is_some() {
            return Err(clash);
        }
        Ok(contained)
    }

    /// Context-threaded `insertConceptThrowClashReturnContained`.
    pub fn insert_concept_throw_clash_return_contained_in_context(
        &mut self,
        ctx: &ProcessContext,
        onto: &OntologyArenas,
        concept_descriptor: ConDescId,
        dep_track_point: TrackPointId,
        reapply_queue_it: Option<&mut CondensedReapplyQueueIterator>,
    ) -> Result<bool, ClashDescId> {
        let mut contained = false;
        let clash = self.insert_concept_return_clash_in_context(
            ctx,
            onto,
            concept_descriptor,
            dep_track_point,
            Some(&mut contained),
            reapply_queue_it,
        );
        if clash.is_some() {
            return Err(clash);
        }
        Ok(contained)
    }

    /// Snapshot a reapply map into a key-SORTED `Vec<LabelSetMapEntry>` — the real
    /// `CReapplyConceptLabelSetIterator` merge logic (`reapply_sat`) walks the two
    /// streams in ascending key order (the C++ holds `CPROCESSMAP::const_iterator`s
    /// into an ORDERED map). The port stores the entries in an unordered `HashMap`,
    /// so the builder sorts on the way out (the W2.7-DEFER the reapply_sat author
    /// flagged on `getConceptLabelSetIterator`).
    fn snapshot_sorted_entries(
        m: &HashMap<Cint64, ConceptDescriptorDependencyReapplyData>,
    ) -> Vec<LabelSetMapEntry> {
        let mut entries: Vec<LabelSetMapEntry> = m
            .iter()
            .map(|(k, v)| LabelSetMapEntry {
                key: *k,
                concept_descriptor: v.concept_descriptor,
                pos_neg_reapply_queue: v.pos_neg_reapply_queue.clone(),
            })
            .collect();
        entries.sort_by_key(|e| e.key);
        entries
    }

    /// Port of `getConceptLabelSetIterator` — now builds the REAL
    /// `reapply_sat::ReapplyConceptLabelSetIterator` (W3b). The faithful branch
    /// structure is:
    ///   if (getSorted||getDependencies||getAllStructure) {
    ///       iterate the merged main + additional reapply maps (linker = nullptr,
    ///       skipEmpty = !getAllStructure)
    ///   } else
    ///       iterate the mConceptDesLinker chain (both maps empty, skipEmpty = true,
    ///       the C++ ctor default).
    pub fn get_concept_label_set_iterator(
        &self,
        get_sorted: bool,
        get_dependencies: bool,
        get_all_structure: bool,
    ) -> ReapplyConceptLabelSetIterator {
        if get_sorted || get_dependencies || get_all_structure {
            let main = Self::snapshot_sorted_entries(&self.concept_des_dep_map);
            // C++: `if (mAdditionalConceptDesDepMap) … addBegin/addEnd … else empty`.
            let additional = match &self.additional_concept_des_dep_map {
                AdditionalDesDepMapRef::Null => Vec::new(),
                AdditionalDesDepMapRef::Owned(m) => Self::snapshot_sorted_entries(m),
                // Arena-free fallback; see `get_concept_label_set_iterator_in_context`.
                AdditionalDesDepMapRef::Shared(_) => Vec::new(),
            };
            ReapplyConceptLabelSetIterator::new(
                self.concept_count,
                ConDescId::NONE,
                main,
                additional,
                !get_all_structure,
            )
        } else {
            ReapplyConceptLabelSetIterator::new(
                self.concept_count,
                self.concept_des_linker,
                Vec::new(),
                Vec::new(),
                true,
            )
        }
    }

    /// Context-threaded `getConceptLabelSetIterator`, following shared additional
    /// aliases for the additional-map `constBegin`/`constEnd` range.
    pub fn get_concept_label_set_iterator_in_context(
        &self,
        ctx: &ProcessContext,
        get_sorted: bool,
        get_dependencies: bool,
        get_all_structure: bool,
    ) -> ReapplyConceptLabelSetIterator {
        if get_sorted || get_dependencies || get_all_structure {
            let main = Self::snapshot_sorted_entries(&self.concept_des_dep_map);
            let additional = match &self.additional_concept_des_dep_map {
                AdditionalDesDepMapRef::Null => Vec::new(),
                AdditionalDesDepMapRef::Owned(m) => Self::snapshot_sorted_entries(m),
                AdditionalDesDepMapRef::Shared(alias) => {
                    Self::additional_alias_map_in_context(ctx, *alias)
                        .map_or_else(Vec::new, Self::snapshot_sorted_entries)
                }
            };
            ReapplyConceptLabelSetIterator::new(
                self.concept_count,
                ConDescId::NONE,
                main,
                additional,
                !get_all_structure,
            )
        } else {
            ReapplyConceptLabelSetIterator::new(
                self.concept_count,
                self.concept_des_linker,
                Vec::new(),
                Vec::new(),
                true,
            )
        }
    }

    /// Port of `getConceptDescriptorAndReapplyQueue(CConcept*, …)`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: Rust callers that need the C++
    /// `reapplyQueue` out-pointer use
    /// `get_concept_descriptor_and_reapply_queue_state_by_tag`, which exposes
    /// the queue state without returning a long-lived borrow into the label-set
    /// map.
    pub fn get_concept_descriptor_and_reapply_queue(
        &self,
        concept: ConceptId,
        con_des: &mut ConDescId,
        dep_track_point: &mut TrackPointId,
    ) -> bool {
        self.get_concept_descriptor_and_reapply_queue_by_tag(
            Self::concept_tag(concept),
            con_des,
            dep_track_point,
        )
    }

    /// Context-threaded `getConceptDescriptorAndReapplyQueue(CConcept*, ...)`.
    pub fn get_concept_descriptor_and_reapply_queue_in_context(
        &self,
        ctx: &ProcessContext,
        onto: &OntologyArenas,
        concept: ConceptId,
        con_des: &mut ConDescId,
        dep_track_point: &mut TrackPointId,
    ) -> bool {
        self.get_concept_descriptor_and_reapply_queue_by_tag_in_context(
            ctx,
            Self::concept_tag_in_ontology(onto, concept),
            con_des,
            dep_track_point,
        )
    }

    /// Port of `getConceptDescriptorAndReapplyQueue(cint64 conTag, …)`.
    pub fn get_concept_descriptor_and_reapply_queue_by_tag(
        &self,
        con_tag: Cint64,
        con_des: &mut ConDescId,
        dep_track_point: &mut TrackPointId,
    ) -> bool {
        let mut con_des_dep_data = self.concept_des_dep_map.get(&con_tag);
        let mut contained = con_des_dep_data.is_some();
        if con_des_dep_data.is_none() && self.additional_is_present() {
            con_des_dep_data = self.additional_get_ref(con_tag);
            contained = con_des_dep_data.is_some();
        }
        if contained {
            let data = con_des_dep_data.unwrap();
            *con_des = data.concept_descriptor;
            // W2-DEFER[api]: reapplyQueue = &data.pos_neg_reapply_queue.
            if con_des.is_some() {
                *dep_track_point = Self::con_des_dep_track_point(*con_des);
            } else {
                *dep_track_point = TrackPointId::NONE;
            }
            contained = con_des.is_some();
        }
        contained
    }

    /// Context-threaded `getConceptDescriptorAndReapplyQueue(cint64 conTag, ...)`.
    pub fn get_concept_descriptor_and_reapply_queue_by_tag_in_context(
        &self,
        ctx: &ProcessContext,
        con_tag: Cint64,
        con_des: &mut ConDescId,
        dep_track_point: &mut TrackPointId,
    ) -> bool {
        let mut con_des_dep_data = self.concept_des_dep_map.get(&con_tag);
        let mut contained = con_des_dep_data.is_some();
        if con_des_dep_data.is_none() && self.additional_is_present() {
            con_des_dep_data = self.additional_get_ref_in_context(ctx, con_tag);
            contained = con_des_dep_data.is_some();
        }
        if contained {
            let data = con_des_dep_data.unwrap();
            *con_des = data.concept_descriptor;
            if con_des.is_some() {
                *dep_track_point = Self::con_des_dep_track_point_in_context(ctx, *con_des);
            } else {
                *dep_track_point = TrackPointId::NONE;
            }
            contained = con_des.is_some();
        }
        contained
    }

    /// Rust-owned port helper for
    /// `getConceptDescriptorAndReapplyQueue(cint64 conTag, ..., CCondensedReapplyQueue*& reapplyQueue)`.
    ///
    /// The C++ caller only needs `reapplyQueue->isEmpty()` before asking the
    /// label set for `getConceptReapplyIterator(bindingConDes)`. Returning the
    /// emptiness bit here preserves that control flow without holding a borrow
    /// across the later iterator creation.
    pub fn get_concept_descriptor_and_reapply_queue_state_by_tag(
        &self,
        con_tag: Cint64,
        con_des: &mut ConDescId,
        dep_track_point: &mut TrackPointId,
        reapply_queue_empty: &mut bool,
    ) -> bool {
        let mut con_des_dep_data = self.concept_des_dep_map.get(&con_tag);
        let mut contained = con_des_dep_data.is_some();
        if con_des_dep_data.is_none() && self.additional_is_present() {
            con_des_dep_data = self.additional_get_ref(con_tag);
            contained = con_des_dep_data.is_some();
        }
        if contained {
            let data = con_des_dep_data.unwrap();
            *con_des = data.concept_descriptor;
            *reapply_queue_empty = Self::queue_is_empty(&data.pos_neg_reapply_queue);
            if con_des.is_some() {
                *dep_track_point = Self::con_des_dep_track_point(*con_des);
            } else {
                *dep_track_point = TrackPointId::NONE;
            }
            contained = con_des.is_some();
        } else {
            *reapply_queue_empty = true;
        }
        contained
    }

    /// Context-threaded read-only helper for
    /// `getConceptDescriptorAndReapplyQueue(cint64 conTag, ..., reapplyQueue)`.
    pub fn get_concept_descriptor_and_reapply_queue_state_by_tag_in_context(
        &self,
        ctx: &ProcessContext,
        con_tag: Cint64,
        con_des: &mut ConDescId,
        dep_track_point: &mut TrackPointId,
        reapply_queue_empty: &mut bool,
    ) -> bool {
        let mut con_des_dep_data = self.concept_des_dep_map.get(&con_tag);
        let mut contained = con_des_dep_data.is_some();
        if con_des_dep_data.is_none() && self.additional_is_present() {
            con_des_dep_data = self.additional_get_ref_in_context(ctx, con_tag);
            contained = con_des_dep_data.is_some();
        }
        if contained {
            let data = con_des_dep_data.unwrap();
            *con_des = data.concept_descriptor;
            *reapply_queue_empty = Self::queue_is_empty(&data.pos_neg_reapply_queue);
            if con_des.is_some() {
                *dep_track_point = Self::con_des_dep_track_point_in_context(ctx, *con_des);
            } else {
                *dep_track_point = TrackPointId::NONE;
            }
            contained = con_des.is_some();
        } else {
            *reapply_queue_empty = true;
        }
        contained
    }

    /// Extract the current dynamic reapply-queue head for `conTag`, clearing it
    /// when requested. This is the context-threaded Rust equivalent of using the
    /// `CCondensedReapplyQueue*` out-param returned by
    /// `getConceptDescriptorAndReapplyQueue` and then calling
    /// `reapplyQueue->getIterator(..., clearDynamicReapplyQueue)`.
    pub fn take_concept_reapply_queue_head_by_tag(
        &mut self,
        con_tag: Cint64,
        clear_dynamic_reapply_queue: bool,
    ) -> super::reapply_sat::CondensedReapplyConceptDescriptorId {
        if let Some(d) = self.concept_des_dep_map.get_mut(&con_tag) {
            let head = d.pos_neg_reapply_queue.dynamic_pos_neg_reapply_des_linker();
            if clear_dynamic_reapply_queue {
                d.pos_neg_reapply_queue
                    .set_dynamic_pos_neg_reapply_des_linker(
                        super::reapply_sat::CondensedReapplyConceptDescriptorId::NONE,
                    );
            }
            return head;
        }
        match &mut self.additional_concept_des_dep_map {
            AdditionalDesDepMapRef::Owned(m) => {
                if let Some(d) = m.get_mut(&con_tag) {
                    let head = d.pos_neg_reapply_queue.dynamic_pos_neg_reapply_des_linker();
                    if clear_dynamic_reapply_queue {
                        d.pos_neg_reapply_queue
                            .set_dynamic_pos_neg_reapply_des_linker(
                                super::reapply_sat::CondensedReapplyConceptDescriptorId::NONE,
                            );
                    }
                    head
                } else {
                    super::reapply_sat::CondensedReapplyConceptDescriptorId::NONE
                }
            }
            // W2-DEFER[api][unclear]: follow the Shared alias.
            _ => super::reapply_sat::CondensedReapplyConceptDescriptorId::NONE,
        }
    }

    /// Port of `getConceptDescriptorOrReapplyQueue(CConcept*, …)`.
    pub fn get_concept_descriptor_or_reapply_queue(
        &self,
        concept: ConceptId,
        con_des: &mut ConDescId,
        dep_track_point: &mut TrackPointId,
    ) -> bool {
        self.get_concept_descriptor_or_reapply_queue_by_tag(
            Self::concept_tag(concept),
            con_des,
            dep_track_point,
        )
    }

    /// Context-threaded `getConceptDescriptorOrReapplyQueue(CConcept*, ...)`.
    pub fn get_concept_descriptor_or_reapply_queue_in_context(
        &self,
        ctx: &ProcessContext,
        onto: &OntologyArenas,
        concept: ConceptId,
        con_des: &mut ConDescId,
        dep_track_point: &mut TrackPointId,
    ) -> bool {
        self.get_concept_descriptor_or_reapply_queue_by_tag_in_context(
            ctx,
            Self::concept_tag_in_ontology(onto, concept),
            con_des,
            dep_track_point,
        )
    }

    /// Port of `getConceptDescriptorOrReapplyQueue(cint64 conTag, …)`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: same `reapplyQueue` out-pointer deferral as above.
    /// The C++ final `contained = conDes != nullptr || reapplyQueue != nullptr;`
    /// is true whenever the entry was found (the queue ref is always non-null when
    /// contained), so it reduces to "entry found".
    pub fn get_concept_descriptor_or_reapply_queue_by_tag(
        &self,
        con_tag: Cint64,
        con_des: &mut ConDescId,
        dep_track_point: &mut TrackPointId,
    ) -> bool {
        let mut con_des_dep_data = self.concept_des_dep_map.get(&con_tag);
        let mut contained = con_des_dep_data.is_some();
        if con_des_dep_data.is_none() && self.additional_is_present() {
            con_des_dep_data = self.additional_get_ref(con_tag);
            contained = con_des_dep_data.is_some();
        }
        if contained {
            let data = con_des_dep_data.unwrap();
            *con_des = data.concept_descriptor;
            // W2-DEFER[api]: reapplyQueue = &data.pos_neg_reapply_queue (always non-null here).
            if con_des.is_some() {
                *dep_track_point = Self::con_des_dep_track_point(*con_des);
            } else {
                *dep_track_point = TrackPointId::NONE;
            }
            // conDes != nullptr || reapplyQueue(=non-null) != nullptr  ==>  true
            let reapply_queue_present = true;
            contained = con_des.is_some() || reapply_queue_present;
        }
        contained
    }

    /// Context-threaded `getConceptDescriptorOrReapplyQueue(cint64 conTag, ...)`.
    pub fn get_concept_descriptor_or_reapply_queue_by_tag_in_context(
        &self,
        ctx: &ProcessContext,
        con_tag: Cint64,
        con_des: &mut ConDescId,
        dep_track_point: &mut TrackPointId,
    ) -> bool {
        let mut con_des_dep_data = self.concept_des_dep_map.get(&con_tag);
        let mut contained = con_des_dep_data.is_some();
        if con_des_dep_data.is_none() && self.additional_is_present() {
            con_des_dep_data = self.additional_get_ref_in_context(ctx, con_tag);
            contained = con_des_dep_data.is_some();
        }
        if contained {
            let data = con_des_dep_data.unwrap();
            *con_des = data.concept_descriptor;
            if con_des.is_some() {
                *dep_track_point = Self::con_des_dep_track_point_in_context(ctx, *con_des);
            } else {
                *dep_track_point = TrackPointId::NONE;
            }
            let reapply_queue_present = true;
            contained = con_des.is_some() || reapply_queue_present;
        }
        contained
    }

    /// Read-only port helper for
    /// `getConceptDescriptorOrReapplyQueue(cint64, conDes, depTrackPoint, reapplyQueue)`.
    ///
    /// Unlike `get_concept_descriptor_and_reapply_queue_state_by_tag`, this keeps
    /// Konclude's "descriptor OR queue" containment semantics and exposes whether
    /// the queue is empty for callers that need `reapplyQueue->isEmpty()`.
    pub fn get_concept_descriptor_or_reapply_queue_state_by_tag(
        &self,
        con_tag: Cint64,
        con_des: &mut ConDescId,
        dep_track_point: &mut TrackPointId,
        reapply_queue_present: &mut bool,
        reapply_queue_empty: &mut bool,
    ) -> bool {
        let mut con_des_dep_data = self.concept_des_dep_map.get(&con_tag);
        let mut contained = con_des_dep_data.is_some();
        if con_des_dep_data.is_none() && self.additional_is_present() {
            con_des_dep_data = self.additional_get_ref(con_tag);
            contained = con_des_dep_data.is_some();
        }
        if contained {
            let data = con_des_dep_data.unwrap();
            *con_des = data.concept_descriptor;
            *reapply_queue_present = true;
            *reapply_queue_empty = Self::queue_is_empty(&data.pos_neg_reapply_queue);
            if con_des.is_some() {
                *dep_track_point = Self::con_des_dep_track_point(*con_des);
            } else {
                *dep_track_point = TrackPointId::NONE;
            }
            contained = con_des.is_some() || *reapply_queue_present;
        } else {
            *con_des = ConDescId::NONE;
            *dep_track_point = TrackPointId::NONE;
            *reapply_queue_present = false;
            *reapply_queue_empty = true;
        }
        contained
    }

    /// Context-threaded read-only helper for
    /// `getConceptDescriptorOrReapplyQueue(cint64, conDes, depTrackPoint, reapplyQueue)`.
    pub fn get_concept_descriptor_or_reapply_queue_state_by_tag_in_context(
        &self,
        ctx: &ProcessContext,
        con_tag: Cint64,
        con_des: &mut ConDescId,
        dep_track_point: &mut TrackPointId,
        reapply_queue_present: &mut bool,
        reapply_queue_empty: &mut bool,
    ) -> bool {
        let mut con_des_dep_data = self.concept_des_dep_map.get(&con_tag);
        let mut contained = con_des_dep_data.is_some();
        if con_des_dep_data.is_none() && self.additional_is_present() {
            con_des_dep_data = self.additional_get_ref_in_context(ctx, con_tag);
            contained = con_des_dep_data.is_some();
        }
        if contained {
            let data = con_des_dep_data.unwrap();
            *con_des = data.concept_descriptor;
            *reapply_queue_present = true;
            *reapply_queue_empty = Self::queue_is_empty(&data.pos_neg_reapply_queue);
            if con_des.is_some() {
                *dep_track_point = Self::con_des_dep_track_point_in_context(ctx, *con_des);
            } else {
                *dep_track_point = TrackPointId::NONE;
            }
            contained = con_des.is_some() || *reapply_queue_present;
        } else {
            *con_des = ConDescId::NONE;
            *dep_track_point = TrackPointId::NONE;
            *reapply_queue_present = false;
            *reapply_queue_empty = true;
        }
        contained
    }

    /// Port of `getConceptDescriptorAndReapplyQueue(CConcept*&, CConceptDescriptor*&, bool create)`
    /// → `CCondensedReapplyQueue*` (`None` == `nullptr`), setting `con_des` out.
    pub fn get_concept_descriptor_and_reapply_queue_create(
        &mut self,
        concept: ConceptId,
        con_des: &mut ConDescId,
        create: bool,
    ) -> Option<&mut CondensedReapplyQueue> {
        let con_tag = Self::concept_tag(concept);
        if create {
            let add_present = self.additional_is_present();
            let existed = self.concept_des_dep_map.contains_key(&con_tag);
            let add_opt = if !existed && add_present {
                self.additional_get_cloned(con_tag)
            } else {
                None
            };
            // tryInsert(conTag, data(nullptr), …).
            let contained = self.concept_des_dep_map.entry(con_tag).or_insert_with(|| {
                ConceptDescriptorDependencyReapplyData {
                    concept_descriptor: ConDescId::NONE,
                    pos_neg_reapply_queue: CondensedReapplyQueue::new(),
                }
            });
            if !existed && add_present {
                if let Some(add) = add_opt {
                    if add.concept_descriptor.is_some()
                        || !Self::queue_is_empty(&add.pos_neg_reapply_queue)
                    {
                        *contained = add;
                    }
                }
            }
            *con_des = contained.concept_descriptor;
            Some(&mut contained.pos_neg_reapply_queue)
        } else {
            if self.concept_des_dep_map.contains_key(&con_tag) {
                *con_des = self
                    .concept_des_dep_map
                    .get(&con_tag)
                    .unwrap()
                    .concept_descriptor;
                return self
                    .concept_des_dep_map
                    .get_mut(&con_tag)
                    .map(|d| &mut d.pos_neg_reapply_queue);
            }
            // additional map: Owned exact, Shared `// W2-DEFER[api]`.
            match &mut self.additional_concept_des_dep_map {
                AdditionalDesDepMapRef::Owned(m) => {
                    if let Some(d) = m.get_mut(&con_tag) {
                        *con_des = d.concept_descriptor;
                        Some(&mut d.pos_neg_reapply_queue)
                    } else {
                        None
                    }
                }
                // W2-DEFER[api][unclear]: follow the Shared alias.
                _ => None,
            }
        }
    }

    /// Port of `getConceptReapplyQueue(cint64 conTag, bool create)`
    /// → `CCondensedReapplyQueue*` (`None` == `nullptr`).
    pub fn get_concept_reapply_queue_by_tag(
        &mut self,
        con_tag: Cint64,
        create: bool,
    ) -> Option<&mut CondensedReapplyQueue> {
        if create {
            let add_present = self.additional_is_present();
            let existed = self.concept_des_dep_map.contains_key(&con_tag);
            let add_opt = if !existed && add_present {
                self.additional_get_cloned(con_tag)
            } else {
                None
            };
            let contained = self.concept_des_dep_map.entry(con_tag).or_insert_with(|| {
                ConceptDescriptorDependencyReapplyData {
                    concept_descriptor: ConDescId::NONE,
                    pos_neg_reapply_queue: CondensedReapplyQueue::new(),
                }
            });
            if !existed && add_present {
                if let Some(add) = add_opt {
                    if add.concept_descriptor.is_some()
                        || !Self::queue_is_empty(&add.pos_neg_reapply_queue)
                    {
                        *contained = add;
                    }
                }
            }
            Some(&mut contained.pos_neg_reapply_queue)
        } else {
            if self.concept_des_dep_map.contains_key(&con_tag) {
                return self
                    .concept_des_dep_map
                    .get_mut(&con_tag)
                    .map(|d| &mut d.pos_neg_reapply_queue);
            }
            match &mut self.additional_concept_des_dep_map {
                AdditionalDesDepMapRef::Owned(m) => {
                    m.get_mut(&con_tag).map(|d| &mut d.pos_neg_reapply_queue)
                }
                // W2-DEFER[api][unclear]: follow the Shared alias.
                _ => None,
            }
        }
    }

    /// Port of `getConceptReapplyQueue(CConcept*&, bool& conceptNegation, bool create)`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: `conceptNegation` is unused in the C++ body (the
    /// pos/neg split is folded into one queue), kept for signature fidelity.
    pub fn get_concept_reapply_queue(
        &mut self,
        concept: ConceptId,
        _concept_negation: bool,
        create: bool,
    ) -> Option<&mut CondensedReapplyQueue> {
        let con_tag = Self::concept_tag(concept);
        self.get_concept_reapply_queue_by_tag(con_tag, create)
    }

    /// Port of `containsConceptReapplyQueue(CConcept*&, bool& conceptNegation)`.
    pub fn contains_concept_reapply_queue(
        &self,
        concept: ConceptId,
        _concept_negation: bool,
    ) -> bool {
        let con_tag = Self::concept_tag(concept);
        if let Some(d) = self.concept_des_dep_map.get(&con_tag) {
            return !Self::queue_is_empty(&d.pos_neg_reapply_queue);
        } else if self.additional_is_present() {
            if let Some(d) = self.additional_get_ref(con_tag) {
                return !Self::queue_is_empty(&d.pos_neg_reapply_queue);
            }
        }
        false
    }

    /// Build the REAL `reapply_sat::CondensedReapplyQueueIterator` from a condensed
    /// reapply-descriptor chain head (the `CCondensedReapplyQueue::getIterator`
    /// result), the `getConceptReapplyIterator` builder that seeds the iterator's
    /// descriptor chain.
    ///
    /// KONCLUDE-PORT-NOTE[api]: `CCondensedReapplyQueue` is still the zero-size
    /// `satellites::CondensedReapplyQueue` placeholder, so it exposes no dynamic
    /// descriptor-linker head yet; every branch seeds `Id::NONE` (an empty real
    /// iterator) until the queue ports its head. The iterator TYPE is real, so the
    /// un-defer wave can walk it via `&ProcessContext`.
    fn build_reapply_iterator(
        ctx: &ProcessContext,
        dynamic_reapply_des_linker: super::reapply_sat::CondensedReapplyConceptDescriptorId,
        concept_negation: bool,
    ) -> super::reapply_sat::CondensedReapplyQueueIterator {
        super::reapply_sat::CondensedReapplyQueueIterator::new_only_positive(
            ctx,
            dynamic_reapply_des_linker,
            !concept_negation,
        )
    }

    /// Port of `getConceptReapplyIterator(CConcept*, bool conceptNegation, bool clearDynamicReapplyQueue)`.
    ///
    /// The `clearDynamicReapplyQueue` path's map mutation (copying an additional-map
    /// entry into the main map: `conDesDepData = *containedConDesDepData;`) IS
    /// ported; the per-branch queue head is `// W2-DEFER[api]` (the
    /// `CCondensedReapplyQueue` placeholder has no head) but the returned iterator
    /// is the REAL `reapply_sat::CondensedReapplyQueueIterator`.
    pub fn get_concept_reapply_iterator(
        &mut self,
        ctx: &ProcessContext,
        concept: ConceptId,
        concept_negation: bool,
        clear_dynamic_reapply_queue: bool,
    ) -> super::reapply_sat::CondensedReapplyQueueIterator {
        let con_tag = Self::concept_tag(concept);
        if self.concept_des_dep_map.contains_key(&con_tag) {
            if !clear_dynamic_reapply_queue {
                // pos_neg_reapply_queue.getIterator(conceptNegation, false).
                let head = self
                    .concept_des_dep_map
                    .get(&con_tag)
                    .map(|d| d.pos_neg_reapply_queue.dynamic_pos_neg_reapply_des_linker())
                    .unwrap_or(super::reapply_sat::CondensedReapplyConceptDescriptorId::NONE);
                return Self::build_reapply_iterator(ctx, head, concept_negation);
            } else {
                // mConceptDesDepMap[conTag].mPosNegReapplyQueue.getIterator(conceptNegation, true).
                let head = if let Some(d) = self.concept_des_dep_map.get_mut(&con_tag) {
                    let head = d.pos_neg_reapply_queue.dynamic_pos_neg_reapply_des_linker();
                    d.pos_neg_reapply_queue
                        .set_dynamic_pos_neg_reapply_des_linker(
                            super::reapply_sat::CondensedReapplyConceptDescriptorId::NONE,
                        );
                    head
                } else {
                    super::reapply_sat::CondensedReapplyConceptDescriptorId::NONE
                };
                return Self::build_reapply_iterator(ctx, head, concept_negation);
            }
        } else if self.additional_is_present() {
            let add_opt = self.additional_get_cloned(con_tag);
            if let Some(add) = add_opt {
                if !clear_dynamic_reapply_queue {
                    // add.pos_neg_reapply_queue.getIterator(conceptNegation, false).
                    let head = add
                        .pos_neg_reapply_queue
                        .dynamic_pos_neg_reapply_des_linker();
                    return Self::build_reapply_iterator(ctx, head, concept_negation);
                } else if !Self::queue_is_empty(&add.pos_neg_reapply_queue) {
                    // conDesDepData = *containedConDesDepData; (copy additional into main)
                    self.concept_des_dep_map.insert(con_tag, add);
                    // getIterator(conceptNegation, true).
                    let head = if let Some(d) = self.concept_des_dep_map.get_mut(&con_tag) {
                        let head = d.pos_neg_reapply_queue.dynamic_pos_neg_reapply_des_linker();
                        d.pos_neg_reapply_queue
                            .set_dynamic_pos_neg_reapply_des_linker(
                                super::reapply_sat::CondensedReapplyConceptDescriptorId::NONE,
                            );
                        head
                    } else {
                        super::reapply_sat::CondensedReapplyConceptDescriptorId::NONE
                    };
                    return Self::build_reapply_iterator(ctx, head, concept_negation);
                } else {
                    // add.pos_neg_reapply_queue.getIterator(conceptNegation, false).
                    let head = add
                        .pos_neg_reapply_queue
                        .dynamic_pos_neg_reapply_des_linker();
                    return Self::build_reapply_iterator(ctx, head, concept_negation);
                }
            }
        }
        // CCondensedReapplyQueueIterator(nullptr, conceptNegation).
        Self::build_reapply_iterator(
            ctx,
            super::reapply_sat::CondensedReapplyConceptDescriptorId::NONE,
            concept_negation,
        )
    }

    /// Context-threaded `getConceptReapplyIterator` variant that can read
    /// `containedConDesDepData` through a `Shared` additional-map alias before
    /// optionally copying it into the main map for the clear-dynamic path.
    pub fn get_concept_reapply_iterator_in_context(
        &mut self,
        ctx: &ProcessContext,
        concept: ConceptId,
        concept_negation: bool,
        clear_dynamic_reapply_queue: bool,
    ) -> super::reapply_sat::CondensedReapplyQueueIterator {
        let con_tag = Self::concept_tag(concept);
        if self.concept_des_dep_map.contains_key(&con_tag) {
            return self.get_concept_reapply_iterator(
                ctx,
                concept,
                concept_negation,
                clear_dynamic_reapply_queue,
            );
        }
        if self.additional_is_present() {
            let add_opt = self.additional_get_cloned_in_context(ctx, con_tag);
            if let Some(add) = add_opt {
                if !clear_dynamic_reapply_queue {
                    let head = add
                        .pos_neg_reapply_queue
                        .dynamic_pos_neg_reapply_des_linker();
                    return Self::build_reapply_iterator(ctx, head, concept_negation);
                } else if !Self::queue_is_empty(&add.pos_neg_reapply_queue) {
                    self.concept_des_dep_map.insert(con_tag, add);
                    let head = if let Some(d) = self.concept_des_dep_map.get_mut(&con_tag) {
                        let head = d.pos_neg_reapply_queue.dynamic_pos_neg_reapply_des_linker();
                        d.pos_neg_reapply_queue
                            .set_dynamic_pos_neg_reapply_des_linker(
                                super::reapply_sat::CondensedReapplyConceptDescriptorId::NONE,
                            );
                        head
                    } else {
                        super::reapply_sat::CondensedReapplyConceptDescriptorId::NONE
                    };
                    return Self::build_reapply_iterator(ctx, head, concept_negation);
                } else {
                    let head = add
                        .pos_neg_reapply_queue
                        .dynamic_pos_neg_reapply_des_linker();
                    return Self::build_reapply_iterator(ctx, head, concept_negation);
                }
            }
        }
        Self::build_reapply_iterator(
            ctx,
            super::reapply_sat::CondensedReapplyConceptDescriptorId::NONE,
            concept_negation,
        )
    }

    /// Port of `getConceptReapplyIterator(CConceptDescriptor*, bool clearDynamicReapplyQueue)`.
    pub fn get_concept_reapply_iterator_des(
        &mut self,
        ctx: &ProcessContext,
        con_des: ConDescId,
        clear_dynamic_reapply_queue: bool,
    ) -> super::reapply_sat::CondensedReapplyQueueIterator {
        // W2-DEFER[api]: conDes->getConcept() / conDes->isNegated() (descriptor arena).
        self.get_concept_reapply_iterator(
            ctx,
            Self::con_des_concept(con_des),
            Self::con_des_negated(con_des),
            clear_dynamic_reapply_queue,
        )
    }

    /// Port of `getAddingSortedConceptDescriptionLinker`.
    pub fn get_adding_sorted_concept_description_linker(&self) -> ConDescId {
        self.concept_des_linker
    }

    /// Port of `getConceptDescriptorDependencyReapplyData(cint64 dataTag)` → `&mut`.
    pub fn get_concept_descriptor_dependency_reapply_data(
        &mut self,
        data_tag: Cint64,
    ) -> &mut ConceptDescriptorDependencyReapplyData {
        let add_present = self.additional_is_present();
        // Pull the additional value out before the &mut borrow.
        let add_opt = if add_present {
            self.additional_get_cloned(data_tag)
        } else {
            None
        };
        // `CConceptDescriptorDependencyReapplyData& conData = mConceptDesDepMap[dataTag];`
        let con_data = self
            .concept_des_dep_map
            .entry(data_tag)
            .or_insert_with(ConceptDescriptorDependencyReapplyData::default);
        if add_present
            && con_data.concept_descriptor.is_none()
            && Self::queue_is_empty(&con_data.pos_neg_reapply_queue)
        {
            if let Some(add) = add_opt {
                *con_data = add;
            }
        }
        con_data
    }
}

#[cfg(test)]
mod tests {
    use super::super::super::model::substrate::INVALID;
    use super::super::super::model::{concept::Concept, ontology::OntologyArenas};
    use super::super::descriptor::ConceptDescriptor;
    use super::super::reapply_sat::CondensedReapplyConceptDescriptor;
    use super::*;

    fn data(concept_descriptor: ConDescId) -> ConceptDescriptorDependencyReapplyData {
        ConceptDescriptorDependencyReapplyData {
            concept_descriptor,
            pos_neg_reapply_queue: CondensedReapplyQueue::new(),
        }
    }

    #[test]
    fn plain_insert_get_clash_updates_signature_only_for_new_descriptor() {
        let mut set = ReapplyConceptLabelSet::new(INVALID);
        let con_des = ConDescId::new(17);

        let contained = set.insert_concept_get_clash(con_des, TrackPointId::NONE, None, None, None);
        assert!(!contained);
        let first_signature = set.get_concept_signature_value();
        assert_ne!(first_signature, 0);

        let contained = set.insert_concept_get_clash(con_des, TrackPointId::NONE, None, None, None);
        assert!(contained);
        assert_eq!(set.get_concept_signature_value(), first_signature);
    }

    #[test]
    fn plain_insert_ignore_clash_updates_signature_on_every_insert() {
        let mut set = ReapplyConceptLabelSet::new(INVALID);
        let con_des = ConDescId::new(19);

        assert!(set.insert_concept_ignore_clash(con_des, TrackPointId::NONE, None));
        let first_signature = set.get_concept_signature_value();
        assert_ne!(first_signature, 0);

        assert!(set.insert_concept_ignore_clash(con_des, TrackPointId::NONE, None));
        assert_ne!(set.get_concept_signature_value(), first_signature);
    }

    fn alloc_concept_with_tag(onto: &mut OntologyArenas, tag: Cint64) -> ConceptId {
        let mut concept = Concept::new();
        concept.set_concept_tag(tag);
        onto.alloc_concept(concept)
    }

    fn alloc_descriptor(
        ctx: &mut ProcessContext,
        concept: ConceptId,
        negated: bool,
        dep_track_point: TrackPointId,
    ) -> ConDescId {
        ctx.alloc_con_desc(ConceptDescriptor {
            concept,
            negated,
            next: ConDescId::NONE,
            dep_track_point,
        })
    }

    #[test]
    fn context_insert_uses_real_concept_tag_and_dependency_track_point() {
        let mut ctx = ProcessContext::new();
        let mut onto = OntologyArenas::new();
        let concept = alloc_concept_with_tag(&mut onto, 7001);
        let dep = TrackPointId::new(44);
        let con_des = alloc_descriptor(&mut ctx, concept, true, dep);
        assert_ne!(con_des.raw, 7001);

        let mut set = ReapplyConceptLabelSet::new(INVALID);
        let contained =
            set.insert_concept_get_clash_in_context(&ctx, &onto, con_des, dep, None, None, None);

        assert!(!contained);
        assert!(set.concept_des_dep_map.contains_key(&7001));
        assert!(!set.concept_des_dep_map.contains_key(&con_des.raw));
        assert!(set.has_concept_in_context(&ctx, &onto, concept, true));
        assert!(!set.has_concept_in_context(&ctx, &onto, concept, false));

        let mut found = ConDescId::NONE;
        let mut found_dep = TrackPointId::NONE;
        assert!(set.get_concept_descriptor_in_context(
            &ctx,
            &onto,
            concept,
            &mut found,
            &mut found_dep
        ));
        assert_eq!(found, con_des);
        assert_eq!(found_dep, dep);
    }

    #[test]
    fn context_insert_get_clash_reports_opposite_descriptor_and_dep_point() {
        let mut ctx = ProcessContext::new();
        let mut onto = OntologyArenas::new();
        let concept = alloc_concept_with_tag(&mut onto, 7101);
        let pos_dep = TrackPointId::new(51);
        let neg_dep = TrackPointId::new(52);
        let pos_des = alloc_descriptor(&mut ctx, concept, false, pos_dep);
        let neg_des = alloc_descriptor(&mut ctx, concept, true, neg_dep);

        let mut set = ReapplyConceptLabelSet::new(INVALID);
        assert!(!set
            .insert_concept_get_clash_in_context(&ctx, &onto, pos_des, pos_dep, None, None, None,));

        let mut clash_des = ConDescId::NONE;
        let mut clash_dep = TrackPointId::NONE;
        assert!(set.insert_concept_get_clash_in_context(
            &ctx,
            &onto,
            neg_des,
            neg_dep,
            None,
            Some(&mut clash_des),
            Some(&mut clash_dep),
        ));
        assert_eq!(clash_des, pos_des);
        assert_eq!(clash_dep, pos_dep);
    }

    #[test]
    fn context_reapply_queue_state_returns_descriptor_dependency() {
        let mut ctx = ProcessContext::new();
        let mut onto = OntologyArenas::new();
        let concept = alloc_concept_with_tag(&mut onto, 7201);
        let dep = TrackPointId::new(61);
        let con_des = alloc_descriptor(&mut ctx, concept, false, dep);

        let mut set = ReapplyConceptLabelSet::new(INVALID);
        assert!(
            !set.insert_concept_get_clash_in_context(&ctx, &onto, con_des, dep, None, None, None,)
        );

        let mut found = ConDescId::NONE;
        let mut found_dep = TrackPointId::NONE;
        let mut queue_empty = false;
        assert!(
            set.get_concept_descriptor_and_reapply_queue_state_by_tag_in_context(
                &ctx,
                7201,
                &mut found,
                &mut found_dep,
                &mut queue_empty,
            )
        );
        assert_eq!(found, con_des);
        assert_eq!(found_dep, dep);
        assert!(queue_empty);
    }

    #[test]
    fn init_in_context_uses_shared_additional_size_for_share_decision() {
        let mut ctx = ProcessContext::new();
        let mut target = ReapplyConceptLabelSet::new(INVALID);
        let mut target_additional = HashMap::new();
        for tag in 1000..1040 {
            target_additional.insert(tag, data(ConDescId::new(tag)));
        }
        target.additional_concept_des_dep_map = AdditionalDesDepMapRef::Owned(target_additional);
        let target_id = ctx.alloc_label_set(target);

        let mut prev = ReapplyConceptLabelSet::new(INVALID);
        prev.additional_concept_des_dep_map = AdditionalDesDepMapRef::Shared(LabelSetMapAlias {
            label_set: target_id,
            which: AdditionalMapSlot::Additional,
        });
        prev.concept_des_dep_map
            .insert(10, data(ConDescId::new(10)));
        prev.concept_des_dep_map
            .insert(11, data(ConDescId::new(11)));
        let prev_id = ctx.alloc_label_set(prev);

        let mut child = ReapplyConceptLabelSet::new(INVALID);
        child.init_concept_label_set_in_context(&ctx, Some((prev_id, ctx.label_set(prev_id))));

        assert!(matches!(
            child.additional_concept_des_dep_map,
            AdditionalDesDepMapRef::Shared(LabelSetMapAlias {
                label_set,
                which: AdditionalMapSlot::Additional,
            }) if label_set == target_id
        ));
        assert_eq!(child.additional_size_in_context(&ctx), 40);
    }

    #[test]
    fn init_in_context_clones_shared_additional_contents_for_rebuild() {
        let mut ctx = ProcessContext::new();
        let mut target = ReapplyConceptLabelSet::new(INVALID);
        let mut target_additional = HashMap::new();
        for tag in 2000..2040 {
            target_additional.insert(tag, data(ConDescId::new(tag)));
        }
        target.additional_concept_des_dep_map = AdditionalDesDepMapRef::Owned(target_additional);
        let target_id = ctx.alloc_label_set(target);

        let mut prev = ReapplyConceptLabelSet::new(INVALID);
        prev.additional_concept_des_dep_map = AdditionalDesDepMapRef::Shared(LabelSetMapAlias {
            label_set: target_id,
            which: AdditionalMapSlot::Additional,
        });
        for tag in 20..30 {
            prev.concept_des_dep_map
                .insert(tag, data(ConDescId::new(tag)));
        }
        let prev_id = ctx.alloc_label_set(prev);

        let mut child = ReapplyConceptLabelSet::new(INVALID);
        child.init_concept_label_set_in_context(&ctx, Some((prev_id, ctx.label_set(prev_id))));

        match &child.additional_concept_des_dep_map {
            AdditionalDesDepMapRef::Owned(m) => {
                assert_eq!(m.len(), 50);
                assert_eq!(
                    m.get(&2000).expect("shared additional").concept_descriptor,
                    ConDescId::new(2000)
                );
                assert_eq!(
                    m.get(&20).expect("prev main").concept_descriptor,
                    ConDescId::new(20)
                );
            }
            _ => panic!("rebuild branch must own the cloned additional contents"),
        }
    }

    #[test]
    fn iterator_in_context_snapshots_shared_additional_alias() {
        let mut ctx = ProcessContext::new();
        let mut target = ReapplyConceptLabelSet::new(INVALID);
        let mut target_additional = HashMap::new();
        target_additional.insert(3000, data(ConDescId::new(300)));
        target.additional_concept_des_dep_map = AdditionalDesDepMapRef::Owned(target_additional);
        let target_id = ctx.alloc_label_set(target);

        let mut set = ReapplyConceptLabelSet::new(INVALID);
        set.additional_concept_des_dep_map = AdditionalDesDepMapRef::Shared(LabelSetMapAlias {
            label_set: target_id,
            which: AdditionalMapSlot::Additional,
        });
        set.concept_count = 1;

        let mut it = set.get_concept_label_set_iterator_in_context(&ctx, true, false, false);
        assert!(it.has_value());
        assert_eq!(it.get_concept_descriptor(), ConDescId::new(300));
        it.move_next(&ctx);
        assert!(!it.has_value());
    }

    #[test]
    fn reapply_iterator_in_context_reads_and_clears_shared_additional_entry() {
        let mut ctx = ProcessContext::new();
        let reapply_head = ctx.alloc_cond_reapply_con_desc(CondensedReapplyConceptDescriptor::new(
            ConDescId::new(400),
            TrackPointId::NONE,
            true,
        ));
        let mut queue = CondensedReapplyQueue::new();
        queue.set_dynamic_pos_neg_reapply_des_linker(reapply_head);

        let mut target = ReapplyConceptLabelSet::new(INVALID);
        let mut target_additional = HashMap::new();
        target_additional.insert(
            4000,
            ConceptDescriptorDependencyReapplyData {
                concept_descriptor: ConDescId::new(400),
                pos_neg_reapply_queue: queue,
            },
        );
        target.additional_concept_des_dep_map = AdditionalDesDepMapRef::Owned(target_additional);
        let target_id = ctx.alloc_label_set(target);

        let mut set = ReapplyConceptLabelSet::new(INVALID);
        set.additional_concept_des_dep_map = AdditionalDesDepMapRef::Shared(LabelSetMapAlias {
            label_set: target_id,
            which: AdditionalMapSlot::Additional,
        });

        let mut it =
            set.get_concept_reapply_iterator_in_context(&ctx, ConceptId::new(4000), false, true);

        assert_eq!(it.next(&ctx, true), reapply_head);
        assert_eq!(
            set.concept_des_dep_map
                .get(&4000)
                .expect("copied into main")
                .pos_neg_reapply_queue
                .dynamic_pos_neg_reapply_des_linker(),
            super::super::reapply_sat::CondensedReapplyConceptDescriptorId::NONE
        );
    }
}
