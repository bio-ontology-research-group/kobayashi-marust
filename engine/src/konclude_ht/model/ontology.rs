//! `model::ontology` — the static terminology arenas.
//!
//! Home of the read-shared `CConcept` / `CRole` / `CIndividual` / `CVariable`
//! objects. In Konclude these live in the terminology (TBox / RBox) built once
//! per ontology and shared read-only across every satisfiability test — they are
//! NOT per-test state and they are NOT pool-allocated from a `CProcessContext`.
//! The process model only ever holds `Id`s (the port of `CConcept*` etc.) that
//! resolve against THESE arenas.
//!
//! KONCLUDE-PORT-NOTE[ownership]: the static/per-test split is faithful — the
//! per-test object pools live in `process::context::ProcessContext`, the static
//! terminology lives here. The accessor convention mirrors `ProcessContext`:
//! `obj->method()` (C++) ≡ `onto.concept(id).method()` (Rust); allocation
//! (`onto.alloc_concept(…)`) happens only during terminology construction, never
//! during a test.

#![allow(dead_code)]

use super::concept::Concept;
use super::concept_process::{
    ConceptProcessData, ConceptSaturationReferenceLinkingData, ReplacementData,
    SaturationConceptReferenceLinking, UnsatisfiableCachingTags,
};
use super::individual::{Individual, Variable};
use super::role::Role;
use super::role_chain::RoleChain;
use super::substrate::{Arena, Cint64, Id, INVALID};
use super::{
    ConceptId, ConceptProcessDataId, ConceptSaturationReferenceLinkingDataId, IndividualId,
    ReplacementDataId, RoleChainId, RoleId, SaturationConceptReferenceLinkingId,
    UnsatisfiableCachingTagsId, VariableId,
};
use std::collections::{HashMap, HashSet};

/// Generate the `get / get_mut / alloc` accessor trio for one terminology arena.
macro_rules! onto_accessors {
    ($field:ident, $ty:ty, $id:ty, $get:ident, $get_mut:ident, $alloc:ident) => {
        /// Resolve an id to a shared borrow (the read path; the common case).
        #[inline]
        pub fn $get(&self, id: $id) -> &$ty {
            self.$field.get(id)
        }
        /// Mutable borrow — used only while building the terminology.
        #[inline]
        pub fn $get_mut(&mut self, id: $id) -> &mut $ty {
            self.$field.get_mut(id)
        }
        /// Allocate a terminology object (construction time only).
        #[inline]
        pub fn $alloc(&mut self, v: $ty) -> $id {
            self.$field.push(v)
        }
    };
}

/// The static terminology: the four read-shared ontology object arenas.
///
/// KONCLUDE-PORT-NOTE[ownership]: held by value alongside the per-test
/// `ProcessContext` only so the calculation context can reach it; semantically
/// it is shared terminology, not per-thread/per-test state.
pub struct OntologyArenas {
    /// `CConcept` pool (the static concept terminology).
    concepts: Arena<Concept>,
    /// `CConceptProcessData` pool.
    concept_process_datas: Arena<ConceptProcessData>,
    /// `CReplacementData` pool.
    replacement_datas: Arena<ReplacementData>,
    /// `CUnsatisfiableCachingTags` pool.
    unsatisfiable_caching_tags: Arena<UnsatisfiableCachingTags>,
    /// `CConceptSaturationReferenceLinkingData` pool.
    concept_saturation_reference_linking_datas: Arena<ConceptSaturationReferenceLinkingData>,
    /// `CSaturationConceptReferenceLinking` pool.
    saturation_concept_reference_linkings: Arena<SaturationConceptReferenceLinking>,
    /// `CRole` pool (the static role / RBox terminology).
    roles: Arena<Role>,
    /// `CRoleChain` pool (`CRBox::mRoleChainVector`; role-automata port).
    role_chains: Arena<RoleChain>,
    /// `CIndividual` pool (the static individuals).
    individuals: Arena<Individual>,
    /// `CABox::mActiveIndividualSet`.
    active_individual_set: Option<HashSet<IndividualId>>,
    /// `COntologyTriplesAssertionsAccessor::getMaxIndexedIndividualId()`.
    max_triples_indexed_individual_id: Cint64,
    /// `CVariable` pool (the static rule variables).
    variables: Arena<Variable>,
    /// `CNominalSchemaTemplate` pool / vector.
    nominal_schema_templates: Arena<NominalSchemaTemplate>,
    /// `CTBox::mEquivConNonCandidateSet`.
    equivalent_concept_non_candidate_set: Option<HashSet<ConceptId>>,
    /// `CMBox::mValueSpacesTriggers`.
    value_spaces_triggers: Option<DatatypeValueSpacesTriggers>,
}

/// `CNominalSchemaTemplate*` → `NominalSchemaTemplateId`.
pub type NominalSchemaTemplateId = Id<NominalSchemaTemplate>;

/// Port of `CDatatypeValueSpacesTriggers`.
///
/// The current classifier gate only observes pointer presence via
/// `CMBox::getValueSpacesTriggers(false)`. The marker keeps that MBox-owned
/// allocation state first-class so later datatype-trigger fields can land here
/// without changing the task/analyser API again.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct DatatypeValueSpacesTriggers;

/// Port of `CNominalSchemaTemplate`.
///
/// KONCLUDE-PORT-NOTE[ownership]: the C++ stores raw `CConcept*` pointers and
/// heap-owned `CBOXSET` / `CBOXHASH` containers. The port stores `ConceptId`s and
/// owned Rust `HashSet` / `HashMap` values with the same membership/lookup
/// semantics. Konclude's `CBOXHASH<CConcept*,CConcept*>` allows multiple values
/// per key and callers iterate `constFind(key)` while the key stays equal; the
/// port stores those values as `Vec<ConceptId>` per key to preserve that
/// behaviour.
pub struct NominalSchemaTemplate {
    /// `CTagItem::mTag`.
    pub tag: Cint64,
    /// `CTerminology* mTerm` — opaque terminology id.
    pub terminology: Cint64,
    /// `CConcept* mTemplConcept`.
    pub template_concept: ConceptId,
    /// `CConcept* mRefConcept`.
    pub reference_concept: ConceptId,
    /// `CBOXSET<CConcept*>* mNomSchemaConSet`.
    pub nominal_schema_concept_set: HashSet<ConceptId>,
    /// `CBOXHASH<CConcept*,CConcept*>* mConceptNomSchemaConceptsHash`.
    pub template_concept_nominal_schema_concept_hash: HashMap<ConceptId, Vec<ConceptId>>,
    /// `CBOXHASH<CConcept*,CConcept*>* mAbsorbableConceptNomSchemaConceptsHash`.
    pub template_absorbable_concept_nominal_schema_concept_hash: HashMap<ConceptId, ConceptId>,
}

impl NominalSchemaTemplate {
    /// Port of `CNominalSchemaTemplate::CNominalSchemaTemplate`.
    pub fn new() -> Self {
        NominalSchemaTemplate {
            tag: 0,
            terminology: INVALID,
            template_concept: ConceptId::NONE,
            reference_concept: ConceptId::NONE,
            nominal_schema_concept_set: HashSet::new(),
            template_concept_nominal_schema_concept_hash: HashMap::new(),
            template_absorbable_concept_nominal_schema_concept_hash: HashMap::new(),
        }
    }

    /// Port of `initNominalSchemaTemplate`.
    pub fn init_nominal_schema_template(
        &mut self,
        nom_schema_con_set: HashSet<ConceptId>,
        concept_nom_schema_concepts_hash: HashMap<ConceptId, Vec<ConceptId>>,
        absorbable_concept_nom_schema_concepts_hash: HashMap<ConceptId, ConceptId>,
    ) -> &mut Self {
        self.template_concept_nominal_schema_concept_hash = concept_nom_schema_concepts_hash;
        self.template_absorbable_concept_nominal_schema_concept_hash =
            absorbable_concept_nom_schema_concepts_hash;
        self.nominal_schema_concept_set = nom_schema_con_set;
        self.terminology = INVALID;
        self.template_concept = ConceptId::NONE;
        self.reference_concept = ConceptId::NONE;
        self.tag = 0;
        self
    }

    /// Port of `setNominalSchemaTemplateTag`.
    pub fn set_nominal_schema_template_tag(&mut self, tag: Cint64) -> &mut Self {
        self.tag = tag;
        self
    }

    /// Port of `getNominalSchemaTemplateTag`.
    pub fn get_nominal_schema_template_tag(&self) -> Cint64 {
        self.tag
    }

    /// Port of `setTerminology`.
    pub fn set_terminology(&mut self, terminology: Cint64) -> &mut Self {
        self.terminology = terminology;
        self
    }

    /// Port of `getTerminology`.
    pub fn get_terminology(&self) -> Cint64 {
        self.terminology
    }

    /// Port of `getTerminologyTag`.
    pub fn get_terminology_tag(&self) -> Cint64 {
        if self.terminology != INVALID {
            self.terminology
        } else {
            0
        }
    }

    /// Port of `setTemplateConcept`.
    pub fn set_template_concept(&mut self, template_concept: ConceptId) -> &mut Self {
        self.template_concept = template_concept;
        self
    }

    /// Port of `getTemplateConcept`.
    pub fn get_template_concept(&self) -> ConceptId {
        self.template_concept
    }

    /// Port of `setReferenceConcept`.
    pub fn set_reference_concept(&mut self, reference_concept: ConceptId) -> &mut Self {
        self.reference_concept = reference_concept;
        self
    }

    /// Port of `getReferenceConcept`.
    pub fn get_reference_concept(&self) -> ConceptId {
        self.reference_concept
    }

    /// Port of `getNominalSchemaConceptSet`.
    pub fn get_nominal_schema_concept_set(&self) -> &HashSet<ConceptId> {
        &self.nominal_schema_concept_set
    }

    /// Port of `setNominalSchemaConceptSet`.
    pub fn set_nominal_schema_concept_set(&mut self, set: HashSet<ConceptId>) -> &mut Self {
        self.nominal_schema_concept_set = set;
        self
    }

    /// Port of `getTemplateConceptNominalSchemaConceptHash`.
    pub fn get_template_concept_nominal_schema_concept_hash(
        &self,
    ) -> &HashMap<ConceptId, Vec<ConceptId>> {
        &self.template_concept_nominal_schema_concept_hash
    }

    /// Port helper for `hash->constFind(concept)` followed by same-key iteration.
    pub fn template_nominal_schema_concepts_for(&self, concept: ConceptId) -> &[ConceptId] {
        self.template_concept_nominal_schema_concept_hash
            .get(&concept)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }

    /// Port of `setTemplateConceptNominalSchemaConceptHash`.
    pub fn set_template_concept_nominal_schema_concept_hash(
        &mut self,
        hash: HashMap<ConceptId, Vec<ConceptId>>,
    ) -> &mut Self {
        self.template_concept_nominal_schema_concept_hash = hash;
        self
    }

    /// Port of `getTemplateAbsorbableConceptNominalSchemaConceptHash`.
    pub fn get_template_absorbable_concept_nominal_schema_concept_hash(
        &self,
    ) -> &HashMap<ConceptId, ConceptId> {
        &self.template_absorbable_concept_nominal_schema_concept_hash
    }

    /// Port of `setTemplateAbsorbableConceptNominalSchemaConceptHash`.
    pub fn set_template_absorbable_concept_nominal_schema_concept_hash(
        &mut self,
        hash: HashMap<ConceptId, ConceptId>,
    ) -> &mut Self {
        self.template_absorbable_concept_nominal_schema_concept_hash = hash;
        self
    }
}

impl Default for NominalSchemaTemplate {
    fn default() -> Self {
        Self::new()
    }
}

impl OntologyArenas {
    pub fn new() -> Self {
        OntologyArenas {
            concepts: Arena::new(),
            concept_process_datas: Arena::new(),
            replacement_datas: Arena::new(),
            unsatisfiable_caching_tags: Arena::new(),
            concept_saturation_reference_linking_datas: Arena::new(),
            saturation_concept_reference_linkings: Arena::new(),
            roles: Arena::new(),
            role_chains: Arena::new(),
            individuals: Arena::new(),
            active_individual_set: None,
            max_triples_indexed_individual_id: 0,
            variables: Arena::new(),
            nominal_schema_templates: Arena::new(),
            equivalent_concept_non_candidate_set: None,
            value_spaces_triggers: None,
        }
    }

    onto_accessors!(
        concepts,
        Concept,
        ConceptId,
        concept,
        concept_mut,
        alloc_concept
    );
    /// Port-facing borrow of the terminology concept vector.
    #[inline]
    pub fn concepts(&self) -> &Arena<Concept> {
        &self.concepts
    }
    onto_accessors!(
        concept_process_datas,
        ConceptProcessData,
        ConceptProcessDataId,
        concept_process_data,
        concept_process_data_mut,
        alloc_concept_process_data
    );
    /// Port-facing borrow of the concept process-data vector.
    #[inline]
    pub fn concept_process_datas(&self) -> &Arena<ConceptProcessData> {
        &self.concept_process_datas
    }
    onto_accessors!(
        replacement_datas,
        ReplacementData,
        ReplacementDataId,
        replacement_data,
        replacement_data_mut,
        alloc_replacement_data
    );
    onto_accessors!(
        unsatisfiable_caching_tags,
        UnsatisfiableCachingTags,
        UnsatisfiableCachingTagsId,
        unsatisfiable_caching_tags,
        unsatisfiable_caching_tags_mut,
        alloc_unsatisfiable_caching_tags
    );
    onto_accessors!(
        concept_saturation_reference_linking_datas,
        ConceptSaturationReferenceLinkingData,
        ConceptSaturationReferenceLinkingDataId,
        concept_saturation_reference_linking_data,
        concept_saturation_reference_linking_data_mut,
        alloc_concept_saturation_reference_linking_data
    );
    /// Port-facing borrow of the concept saturation-reference-linking data vector.
    #[inline]
    pub fn concept_saturation_reference_linking_datas(
        &self,
    ) -> &Arena<ConceptSaturationReferenceLinkingData> {
        &self.concept_saturation_reference_linking_datas
    }
    onto_accessors!(
        saturation_concept_reference_linkings,
        SaturationConceptReferenceLinking,
        SaturationConceptReferenceLinkingId,
        saturation_concept_reference_linking,
        saturation_concept_reference_linking_mut,
        alloc_saturation_concept_reference_linking
    );
    /// Port-facing borrow of the saturation concept-reference-linking vector.
    #[inline]
    pub fn saturation_concept_reference_linkings(
        &self,
    ) -> &Arena<SaturationConceptReferenceLinking> {
        &self.saturation_concept_reference_linkings
    }
    /// Port-facing `CConceptVector::getItemCount`.
    #[inline]
    pub fn concept_count(&self) -> Cint64 {
        self.concepts.len() as Cint64
    }
    onto_accessors!(roles, Role, RoleId, role, role_mut, alloc_role);
    /// Port-facing borrow of the role vector.
    #[inline]
    pub fn roles(&self) -> &Arena<Role> {
        &self.roles
    }
    /// Port-facing `CRoleVector::getItemCount`.
    #[inline]
    pub fn role_count(&self) -> Cint64 {
        self.roles.len() as Cint64
    }
    onto_accessors!(
        role_chains,
        RoleChain,
        RoleChainId,
        role_chain,
        role_chain_mut,
        alloc_role_chain
    );
    /// Port-facing `CRoleChainVector::getItemCount`.
    #[inline]
    pub fn role_chain_count(&self) -> Cint64 {
        self.role_chains.len() as Cint64
    }
    onto_accessors!(
        individuals,
        Individual,
        IndividualId,
        individual,
        individual_mut,
        alloc_individual
    );
    /// Port-facing iteration over `CIndividualVector::getData(i)` entries.
    #[inline]
    pub fn individual_iter(&self) -> std::slice::Iter<'_, Individual> {
        self.individuals.iter()
    }
    /// Port-facing `CIndividualVector::getData(i)`.
    #[inline]
    pub fn individual_data(&self, index: Cint64) -> IndividualId {
        if index >= 0 && (index as usize) < self.individuals.len() {
            IndividualId::new(index)
        } else {
            IndividualId::NONE
        }
    }
    /// Port-facing `CABox::getIndividualCount`.
    #[inline]
    pub fn individual_count(&self) -> Cint64 {
        self.individuals.len() as Cint64
    }
    /// Port of `CABox::getActiveIndividualSet(false)`.
    #[inline]
    pub fn get_active_individual_set(&self) -> Option<&HashSet<IndividualId>> {
        self.active_individual_set.as_ref()
    }

    /// Port of `CABox::getActiveIndividualSet(create)`.
    #[inline]
    pub fn get_active_individual_set_mut(
        &mut self,
        create: bool,
    ) -> Option<&mut HashSet<IndividualId>> {
        if self.active_individual_set.is_none() && create {
            self.active_individual_set = Some(HashSet::new());
        }
        self.active_individual_set.as_mut()
    }

    /// Port helper for `CABox::getActiveIndividualSet(true)->insert`.
    #[inline]
    pub fn insert_active_individual(&mut self, individual: IndividualId) -> bool {
        self.get_active_individual_set_mut(true)
            .expect("created active individual set")
            .insert(individual)
    }

    /// Port helper for `activeIndiSet->contains(indi)`.
    #[inline]
    pub fn is_active_individual(&self, individual: IndividualId) -> bool {
        self.active_individual_set
            .as_ref()
            .is_some_and(|set| set.contains(&individual))
    }

    /// Port of `COntologyTriplesAssertionsAccessor::getMaxIndexedIndividualId`.
    #[inline]
    pub fn get_max_triples_indexed_individual_id(&self) -> Cint64 {
        self.max_triples_indexed_individual_id
    }

    /// Port-side setter for the triple-assertion accessor's max indexed id.
    #[inline]
    pub fn set_max_triples_indexed_individual_id(&mut self, index: Cint64) -> &mut Self {
        self.max_triples_indexed_individual_id = index;
        self
    }
    /// Port of `CTBox::getEquivalentConceptNonCandidateSet(false)`.
    #[inline]
    pub fn get_equivalent_concept_non_candidate_set(&self) -> Option<&HashSet<ConceptId>> {
        self.equivalent_concept_non_candidate_set.as_ref()
    }

    /// Port of `CTBox::getEquivalentConceptNonCandidateSet(create)`.
    #[inline]
    pub fn get_equivalent_concept_non_candidate_set_mut(
        &mut self,
        create: bool,
    ) -> Option<&mut HashSet<ConceptId>> {
        if self.equivalent_concept_non_candidate_set.is_none() && create {
            self.equivalent_concept_non_candidate_set = Some(HashSet::new());
        }
        self.equivalent_concept_non_candidate_set.as_mut()
    }

    /// Port helper for `CTBox::getEquivalentConceptNonCandidateSet(true)->insert`.
    #[inline]
    pub fn insert_equivalent_concept_non_candidate(&mut self, concept: ConceptId) -> bool {
        self.get_equivalent_concept_non_candidate_set_mut(true)
            .expect("created equivalent non-candidate set")
            .insert(concept)
    }

    /// Port of `CMBox::getValueSpacesTriggers(false)`.
    #[inline]
    pub fn get_value_spaces_triggers(&self) -> Option<&DatatypeValueSpacesTriggers> {
        self.value_spaces_triggers.as_ref()
    }

    /// Port of `CMBox::getValueSpacesTriggers(create)`.
    #[inline]
    pub fn get_value_spaces_triggers_mut(
        &mut self,
        create: bool,
    ) -> Option<&mut DatatypeValueSpacesTriggers> {
        if self.value_spaces_triggers.is_none() && create {
            self.value_spaces_triggers = Some(DatatypeValueSpacesTriggers);
        }
        self.value_spaces_triggers.as_mut()
    }

    /// Port helper for the analyser's `getValueSpacesTriggers(false)` branch.
    #[inline]
    pub fn has_value_spaces_triggers(&self) -> bool {
        self.get_value_spaces_triggers().is_some()
    }

    onto_accessors!(
        variables,
        Variable,
        VariableId,
        variable,
        variable_mut,
        alloc_variable
    );
    onto_accessors!(
        nominal_schema_templates,
        NominalSchemaTemplate,
        NominalSchemaTemplateId,
        nominal_schema_template,
        nominal_schema_template_mut,
        alloc_nominal_schema_template
    );

    /// Port-facing `CNominalSchemaTemplateVector::getData`.
    ///
    /// Konclude stores the template id in `CConcept::getParameter()`. In the
    /// arena port, ids are one-based indexes, so non-positive parameters map to
    /// `Id::NONE`.
    pub fn nominal_schema_template_data(&self, template_id: Cint64) -> NominalSchemaTemplateId {
        if template_id >= 0 {
            NominalSchemaTemplateId::new(template_id)
        } else {
            NominalSchemaTemplateId::NONE
        }
    }
}

impl Default for OntologyArenas {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ontology_individual_count_tracks_abox_individual_arena_size() {
        let mut arenas = OntologyArenas::new();
        assert_eq!(arenas.individual_count(), 0);
        arenas.alloc_individual(Individual::new(0));
        arenas.alloc_individual(Individual::new(1));
        assert_eq!(arenas.individual_count(), 2);
    }

    #[test]
    fn nominal_schema_template_init_and_accessors_match_konclude_fields() {
        let mut arenas = OntologyArenas::new();
        let template_concept = arenas.alloc_concept(Concept::new());
        let reference_concept = arenas.alloc_concept(Concept::new());
        let nominal_schema_concept = arenas.alloc_concept(Concept::new());
        let mapped_template_concept = arenas.alloc_concept(Concept::new());
        let mapped_nominal_schema_concept = arenas.alloc_concept(Concept::new());
        let absorbable_concept = arenas.alloc_concept(Concept::new());

        let mut set = HashSet::new();
        set.insert(nominal_schema_concept);
        let mut hash = HashMap::new();
        hash.insert(mapped_template_concept, vec![mapped_nominal_schema_concept]);
        let mut absorbable_hash = HashMap::new();
        absorbable_hash.insert(absorbable_concept, nominal_schema_concept);

        let mut templ = NominalSchemaTemplate::new();
        templ
            .init_nominal_schema_template(set.clone(), hash.clone(), absorbable_hash.clone())
            .set_nominal_schema_template_tag(17)
            .set_terminology(23)
            .set_template_concept(template_concept)
            .set_reference_concept(reference_concept);

        assert_eq!(templ.get_nominal_schema_template_tag(), 17);
        assert_eq!(templ.get_terminology(), 23);
        assert_eq!(templ.get_terminology_tag(), 23);
        assert_eq!(templ.get_template_concept(), template_concept);
        assert_eq!(templ.get_reference_concept(), reference_concept);
        assert_eq!(templ.get_nominal_schema_concept_set(), &set);
        assert_eq!(
            templ.get_template_concept_nominal_schema_concept_hash(),
            &hash
        );
        assert_eq!(
            templ.template_nominal_schema_concepts_for(mapped_template_concept),
            &[mapped_nominal_schema_concept]
        );
        assert!(templ
            .template_nominal_schema_concepts_for(reference_concept)
            .is_empty());
        assert_eq!(
            templ.get_template_absorbable_concept_nominal_schema_concept_hash(),
            &absorbable_hash
        );
    }

    #[test]
    fn nominal_schema_template_preserves_multi_values_for_template_concepts() {
        let mut arenas = OntologyArenas::new();
        let template_concept = arenas.alloc_concept(Concept::new());
        let nominal_schema_concept_a = arenas.alloc_concept(Concept::new());
        let nominal_schema_concept_b = arenas.alloc_concept(Concept::new());

        let mut hash = HashMap::new();
        hash.insert(
            template_concept,
            vec![nominal_schema_concept_a, nominal_schema_concept_b],
        );

        let mut templ = NominalSchemaTemplate::new();
        templ.set_template_concept_nominal_schema_concept_hash(hash);

        assert_eq!(
            templ.template_nominal_schema_concepts_for(template_concept),
            &[nominal_schema_concept_a, nominal_schema_concept_b]
        );
    }

    #[test]
    fn nominal_schema_template_vector_parameter_maps_to_arena_id() {
        let mut arenas = OntologyArenas::new();
        let template_concept = arenas.alloc_concept(Concept::new());
        let mut templ = NominalSchemaTemplate::new();
        templ.set_template_concept(template_concept);
        let templ_id = arenas.alloc_nominal_schema_template(templ);

        assert_eq!(
            arenas.nominal_schema_template_data(templ_id.raw),
            templ_id,
            "CConcept::getParameter stores the nominal-schema template vector id"
        );
        assert_eq!(
            arenas.nominal_schema_template_data(0),
            templ_id,
            "the first arena slot matches Konclude's vector id 0"
        );
        assert!(arenas.nominal_schema_template_data(-1).is_none());
        assert_eq!(
            arenas
                .nominal_schema_template(templ_id)
                .get_template_concept(),
            template_concept
        );
    }

    #[test]
    fn ontology_equivalent_concept_non_candidate_set_matches_tbox_lazy_create() {
        let mut arenas = OntologyArenas::new();
        let concept = arenas.alloc_concept(Concept::new());

        assert!(arenas.get_equivalent_concept_non_candidate_set().is_none());
        assert!(arenas
            .get_equivalent_concept_non_candidate_set_mut(false)
            .is_none());

        assert!(arenas.insert_equivalent_concept_non_candidate(concept));
        assert!(!arenas.insert_equivalent_concept_non_candidate(concept));
        assert!(arenas
            .get_equivalent_concept_non_candidate_set()
            .expect("created equivalent non-candidate set")
            .contains(&concept));
        assert_eq!(
            arenas
                .get_equivalent_concept_non_candidate_set()
                .expect("created equivalent non-candidate set")
                .len(),
            1
        );
    }

    #[test]
    fn ontology_value_spaces_triggers_match_mbox_lazy_create() {
        let mut arenas = OntologyArenas::new();

        assert!(arenas.get_value_spaces_triggers().is_none());
        assert!(arenas.get_value_spaces_triggers_mut(false).is_none());
        assert!(!arenas.has_value_spaces_triggers());

        assert!(arenas.get_value_spaces_triggers_mut(true).is_some());
        assert!(arenas.get_value_spaces_triggers().is_some());
        assert!(arenas.has_value_spaces_triggers());
        assert!(arenas.get_value_spaces_triggers_mut(false).is_some());
    }
}
