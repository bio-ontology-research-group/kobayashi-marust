//! `process::grounding_hash` — nominal-schema grounding reuse cache.
//!
//! Ports:
//!   * `CConceptNominalSchemaGroundingData.{h,cpp}`
//!   * `CConceptNominalSchemaGroundingHasher.{h,cpp}`
//!   * `CConceptNominalSchemaGroundingHash.{h,cpp}`

#![allow(dead_code)]

use super::super::model::substrate::{Cint64, Id, INVALID};
use super::super::model::ConceptId;
use std::collections::HashMap;

/// `CConceptNominalSchemaGroundingData*` → `ConceptNominalSchemaGroundingDataId`.
pub type ConceptNominalSchemaGroundingDataId = Id<ConceptNominalSchemaGroundingData>;
/// `CConceptNominalSchemaGroundingHash*` → `ConceptNominalSchemaGroundingHashId`.
pub type ConceptNominalSchemaGroundingHashId = Id<ConceptNominalSchemaGroundingHash>;

/// Port of `CConceptNominalSchemaGroundingData`.
///
/// KONCLUDE-PORT-NOTE[ownership]: `CPROCESSLIST<CConcept*>` is represented by a
/// `Vec<ConceptId>` in the same ordered traversal used by `isEquivalentTo`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConceptNominalSchemaGroundingData {
    /// `CConcept* mGroundedConcept`.
    pub grounded_concept: ConceptId,
    /// `CConcept* mGroundingConcept`.
    pub grounding_concept: ConceptId,
    /// `CPROCESSLIST<CConcept*> mBindedNomSchConList`.
    pub binded_nominal_schema_concept_list: Vec<ConceptId>,
}

impl ConceptNominalSchemaGroundingData {
    /// Port of `CConceptNominalSchemaGroundingData::CConceptNominalSchemaGroundingData`.
    pub fn new() -> Self {
        ConceptNominalSchemaGroundingData {
            grounded_concept: ConceptId::NONE,
            grounding_concept: ConceptId::NONE,
            binded_nominal_schema_concept_list: Vec::new(),
        }
    }

    /// Port of `setGroundingConcept`.
    pub fn set_grounding_concept(&mut self, concept: ConceptId) -> &mut Self {
        self.grounding_concept = concept;
        self
    }

    /// Port of `setGroundedConcept`.
    pub fn set_grounded_concept(&mut self, concept: ConceptId) -> &mut Self {
        self.grounded_concept = concept;
        self
    }

    /// Port of `addBindedNominalSchemaConcept`.
    pub fn add_binded_nominal_schema_concept(&mut self, concept: ConceptId) -> &mut Self {
        self.binded_nominal_schema_concept_list.push(concept);
        self
    }

    /// Port of `getBindedNominalSchemaConceptList`.
    pub fn get_binded_nominal_schema_concept_list(&self) -> &[ConceptId] {
        &self.binded_nominal_schema_concept_list
    }

    /// Port of `getGroundedConcept`.
    pub fn get_grounded_concept(&self) -> ConceptId {
        self.grounded_concept
    }

    /// Port of `getGroundingConcept`.
    pub fn get_grounding_concept(&self) -> ConceptId {
        self.grounding_concept
    }

    /// Port of `calculateHashValue`.
    pub fn calculate_hash_value(&self) -> Cint64 {
        let mut hash_value = self.grounding_concept.raw;
        let mut multiplier: Cint64 = 13;
        for concept in self.binded_nominal_schema_concept_list.iter() {
            hash_value = hash_value.wrapping_add(multiplier.wrapping_mul(concept.raw));
            multiplier = multiplier.wrapping_mul(2).wrapping_add(1);
        }
        hash_value
    }

    /// Port of `isEquivalentTo`.
    pub fn is_equivalent_to(&self, data: &ConceptNominalSchemaGroundingData) -> bool {
        self.grounding_concept == data.grounding_concept
            && self.binded_nominal_schema_concept_list == data.binded_nominal_schema_concept_list
    }
}

impl Default for ConceptNominalSchemaGroundingData {
    fn default() -> Self {
        Self::new()
    }
}

/// Port of `CConceptNominalSchemaGroundingHasher`.
///
/// The C++ object stores a pointer to data plus its calculated hash. The port
/// stores the same equivalence key by value for use in Rust hash buckets.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ConceptNominalSchemaGroundingKey {
    pub grounding_concept: ConceptId,
    pub binded_nominal_schema_concept_list: Vec<ConceptId>,
}

impl ConceptNominalSchemaGroundingKey {
    /// Port of `CConceptNominalSchemaGroundingHasher(CConceptNominalSchemaGroundingData*)`.
    pub fn new(data: &ConceptNominalSchemaGroundingData) -> Self {
        ConceptNominalSchemaGroundingKey {
            grounding_concept: data.grounding_concept,
            binded_nominal_schema_concept_list: data.binded_nominal_schema_concept_list.clone(),
        }
    }
}

/// Port of `CConceptNominalSchemaGroundingHash`.
#[derive(Clone, Debug)]
pub struct ConceptNominalSchemaGroundingHash {
    pub process_context: Cint64,
    pub map: HashMap<ConceptNominalSchemaGroundingKey, ConceptNominalSchemaGroundingData>,
}

impl ConceptNominalSchemaGroundingHash {
    /// Port of `CConceptNominalSchemaGroundingHash(CProcessContext*)`.
    pub fn new(process_context: Cint64) -> Self {
        ConceptNominalSchemaGroundingHash {
            process_context,
            map: HashMap::new(),
        }
    }

    /// Port of `initConceptNominalSchemaGroundingHash`.
    pub fn init_concept_nominal_schema_grounding_hash(
        &mut self,
        prev_hash: Option<&ConceptNominalSchemaGroundingHash>,
    ) -> &mut Self {
        if let Some(prev) = prev_hash {
            self.map = prev.map.clone();
        } else {
            self.map.clear();
        }
        self
    }

    /// Port-facing equivalent of `value(CConceptNominalSchemaGroundingHasher(...), nullptr)`.
    pub fn value(
        &self,
        data: &ConceptNominalSchemaGroundingData,
    ) -> Option<&ConceptNominalSchemaGroundingData> {
        self.map.get(&ConceptNominalSchemaGroundingKey::new(data))
    }

    /// Port-facing equivalent of `insert(CConceptNominalSchemaGroundingHasher(...), data)`.
    pub fn insert(&mut self, data: ConceptNominalSchemaGroundingData) {
        self.map
            .insert(ConceptNominalSchemaGroundingKey::new(&data), data);
    }
}

impl Default for ConceptNominalSchemaGroundingHash {
    fn default() -> Self {
        Self::new(INVALID)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn concept_nominal_schema_grounding_data_hashes_by_grounding_and_bound_list() {
        let grounding = ConceptId::new(1);
        let bound_a = ConceptId::new(2);
        let bound_b = ConceptId::new(3);
        let grounded = ConceptId::new(4);

        let mut data = ConceptNominalSchemaGroundingData::new();
        data.set_grounding_concept(grounding)
            .set_grounded_concept(grounded)
            .add_binded_nominal_schema_concept(bound_a)
            .add_binded_nominal_schema_concept(bound_b);

        let mut equivalent = ConceptNominalSchemaGroundingData::new();
        equivalent
            .set_grounding_concept(grounding)
            .add_binded_nominal_schema_concept(bound_a)
            .add_binded_nominal_schema_concept(bound_b);

        let mut different_order = ConceptNominalSchemaGroundingData::new();
        different_order
            .set_grounding_concept(grounding)
            .add_binded_nominal_schema_concept(bound_b)
            .add_binded_nominal_schema_concept(bound_a);

        assert!(data.is_equivalent_to(&equivalent));
        assert!(!data.is_equivalent_to(&different_order));

        let mut hash = ConceptNominalSchemaGroundingHash::new(INVALID);
        hash.insert(data.clone());
        assert_eq!(
            hash.value(&equivalent).unwrap().get_grounded_concept(),
            grounded
        );
        assert!(hash.value(&different_order).is_none());
    }

    #[test]
    fn concept_nominal_schema_grounding_hash_init_copies_previous_entries() {
        let mut data = ConceptNominalSchemaGroundingData::new();
        data.set_grounding_concept(ConceptId::new(10))
            .set_grounded_concept(ConceptId::new(11))
            .add_binded_nominal_schema_concept(ConceptId::new(12));

        let mut prev = ConceptNominalSchemaGroundingHash::new(INVALID);
        prev.insert(data.clone());
        let mut next = ConceptNominalSchemaGroundingHash::new(INVALID);
        next.init_concept_nominal_schema_grounding_hash(Some(&prev));

        assert_eq!(
            next.value(&data).unwrap().get_grounded_concept(),
            ConceptId::new(11)
        );
    }
}
