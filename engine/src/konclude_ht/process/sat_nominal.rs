//! Saturation nominal process satellites.
//!
//! Ports saturation nominal sets and dependent-node hash satellites.

#![allow(dead_code)]

use std::collections::{BTreeMap, BTreeSet};

use super::super::model::substrate::{Cint64, Id, INVALID};
use super::SatNodeId;

/// `CSaturationInfluencedNominalSet*`.
pub type SaturationInfluencedNominalSetId = Id<SaturationInfluencedNominalSet>;
/// `CSaturationNominalDependentNodeData*`.
pub type SaturationNominalDependentNodeDataId = Id<SaturationNominalDependentNodeData>;
/// `CSaturationNominalDependentNodeHash*`.
pub type SaturationNominalDependentNodeHashId = Id<SaturationNominalDependentNodeHash>;

/// Port of `CSaturationNominalDependentNodeData::NOMINALCONNECTIONTYPE`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum SaturationNominalConnectionType {
    #[default]
    NoneConnection,
    ValueConnection,
    NominalConnection,
    Opaque(Cint64),
}

impl From<Cint64> for SaturationNominalConnectionType {
    fn from(value: Cint64) -> Self {
        match value {
            0 => Self::NoneConnection,
            1 => Self::ValueConnection,
            2 => Self::NominalConnection,
            other => Self::Opaque(other),
        }
    }
}

impl SaturationNominalConnectionType {
    pub fn as_cint64(self) -> Cint64 {
        match self {
            Self::NoneConnection => 0,
            Self::ValueConnection => 1,
            Self::NominalConnection => 2,
            Self::Opaque(value) => value,
        }
    }
}

/// Port of `CSaturationNominalDependentNodeData`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SaturationNominalDependentNodeData {
    /// `mIndiSatProcData`.
    pub dependent_individual_saturation_node: SatNodeId,
    /// `mConnectionType`.
    pub nominal_connection_type: SaturationNominalConnectionType,
    /// `CLinkerBase::mNext`.
    pub next: SaturationNominalDependentNodeDataId,
    /// `mProcessContext` opaque back handle.
    pub process_context: Cint64,
}

impl Default for SaturationNominalDependentNodeData {
    fn default() -> Self {
        Self::new(INVALID)
    }
}

impl SaturationNominalDependentNodeData {
    /// Port of the constructor.
    pub fn new(process_context: Cint64) -> Self {
        Self {
            dependent_individual_saturation_node: SatNodeId::NONE,
            nominal_connection_type: SaturationNominalConnectionType::NoneConnection,
            next: SaturationNominalDependentNodeDataId::NONE,
            process_context,
        }
    }

    /// Port of `initNominalDependentNodeData`.
    pub fn init_nominal_dependent_node_data(
        &mut self,
        indi_sat_proc_data: SatNodeId,
        connection_type: SaturationNominalConnectionType,
    ) -> &mut Self {
        self.dependent_individual_saturation_node = indi_sat_proc_data;
        self.nominal_connection_type = connection_type;
        self.next = SaturationNominalDependentNodeDataId::NONE;
        self
    }

    /// Port of `getNominalConnectionType`.
    pub fn get_nominal_connection_type(&self) -> SaturationNominalConnectionType {
        self.nominal_connection_type
    }

    /// Port of `setNominalConnectionType`.
    pub fn set_nominal_connection_type(
        &mut self,
        connection_type: SaturationNominalConnectionType,
    ) -> &mut Self {
        self.nominal_connection_type = connection_type;
        self
    }

    /// Port of `getNextNominalConnectionTypeData`.
    pub fn get_next_nominal_connection_type_data(&self) -> SaturationNominalDependentNodeDataId {
        self.next
    }

    /// Port of `getDependentIndividualSaturationNode`.
    pub fn get_dependent_individual_saturation_node(&self) -> SatNodeId {
        self.dependent_individual_saturation_node
    }

    /// Port of `setDependentIndividualSaturationNode`.
    pub fn set_dependent_individual_saturation_node(
        &mut self,
        indi_sat_node: SatNodeId,
    ) -> &mut Self {
        self.dependent_individual_saturation_node = indi_sat_node;
        self
    }

    /// Port of `CLinkerBase::append`.
    pub fn append(&mut self, next: SaturationNominalDependentNodeDataId) -> &mut Self {
        self.next = next;
        self
    }
}

/// Port of `CSaturationNominalDependentNodeHashData`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SaturationNominalDependentNodeHashData {
    /// `mNominalDependentNodeData`.
    pub nominal_dependent_node_data: SaturationNominalDependentNodeDataId,
}

impl Default for SaturationNominalDependentNodeHashData {
    fn default() -> Self {
        Self {
            nominal_dependent_node_data: SaturationNominalDependentNodeDataId::NONE,
        }
    }
}

/// Port of `CSaturationNominalDependentNodeHash`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SaturationNominalDependentNodeHash {
    /// `mNominalDependentNodeDataHash`.
    pub nominal_dependent_node_data_hash: BTreeMap<Cint64, SaturationNominalDependentNodeHashData>,
    /// `mProcessContext` opaque back handle.
    pub process_context: Cint64,
}

impl Default for SaturationNominalDependentNodeHash {
    fn default() -> Self {
        Self::new(INVALID)
    }
}

impl SaturationNominalDependentNodeHash {
    /// Port of the constructor.
    pub fn new(process_context: Cint64) -> Self {
        Self {
            nominal_dependent_node_data_hash: BTreeMap::new(),
            process_context,
        }
    }

    /// Port of `initNominalDependentNodeHash`.
    pub fn init_nominal_dependent_node_hash(
        &mut self,
        nominal_dependent_hash: Option<&SaturationNominalDependentNodeHash>,
    ) -> &mut Self {
        if let Some(hash) = nominal_dependent_hash {
            self.nominal_dependent_node_data_hash = hash.nominal_dependent_node_data_hash.clone();
        } else {
            self.nominal_dependent_node_data_hash.clear();
        }
        self
    }

    /// Port of `getNominalDependentNodeData`.
    pub fn get_nominal_dependent_node_data(
        &self,
        nominal_id: Cint64,
    ) -> SaturationNominalDependentNodeDataId {
        self.nominal_dependent_node_data_hash
            .get(&nominal_id)
            .map_or(SaturationNominalDependentNodeDataId::NONE, |data| {
                data.nominal_dependent_node_data
            })
    }

    /// Port of `addNominalDependentNodeData`.
    pub fn add_nominal_dependent_node_data(
        &mut self,
        nominal_id: Cint64,
        dependent_node_data: SaturationNominalDependentNodeDataId,
    ) -> SaturationNominalDependentNodeDataId {
        let hash_data = self
            .nominal_dependent_node_data_hash
            .entry(nominal_id)
            .or_default();
        let old_head = hash_data.nominal_dependent_node_data;
        hash_data.nominal_dependent_node_data = dependent_node_data;
        old_head
    }
}

/// Port of `CSaturationInfluencedNominalSet`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SaturationInfluencedNominalSet {
    /// Inherited `CPROCESSSET<cint64>`.
    pub nominal_ids: BTreeSet<Cint64>,
    /// `mProcessContext` opaque back handle.
    pub process_context: Cint64,
}

impl Default for SaturationInfluencedNominalSet {
    fn default() -> Self {
        Self::new(INVALID)
    }
}

impl SaturationInfluencedNominalSet {
    /// Port of the constructor.
    pub fn new(process_context: Cint64) -> Self {
        Self {
            nominal_ids: BTreeSet::new(),
            process_context,
        }
    }

    /// Port of `initInfluencedNominalSet`.
    pub fn init_influenced_nominal_set(
        &mut self,
        nominal_set: Option<&SaturationInfluencedNominalSet>,
    ) -> &mut Self {
        if let Some(set) = nominal_set {
            self.nominal_ids = set.nominal_ids.clone();
        } else {
            self.nominal_ids.clear();
        }
        self
    }

    /// Port of `setNominalInfluenced`.
    pub fn set_nominal_influenced(&mut self, nominal_id: Cint64) -> bool {
        self.nominal_ids.insert(nominal_id)
    }

    /// Port of `isNominalInfluenced`.
    pub fn is_nominal_influenced(&self, nominal_id: Cint64) -> bool {
        self.nominal_ids.contains(&nominal_id)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn influenced_nominal_set_reports_first_insert_only() {
        let mut set = SaturationInfluencedNominalSet::new(INVALID);

        assert!(!set.is_nominal_influenced(7));
        assert!(set.set_nominal_influenced(7));
        assert!(set.is_nominal_influenced(7));
        assert!(!set.set_nominal_influenced(7));
    }

    #[test]
    fn influenced_nominal_set_copies_membership() {
        let mut source = SaturationInfluencedNominalSet::new(INVALID);
        source.set_nominal_influenced(3);

        let mut target = SaturationInfluencedNominalSet::new(INVALID);
        target.init_influenced_nominal_set(Some(&source));

        assert!(target.is_nominal_influenced(3));
        source.set_nominal_influenced(5);
        assert!(!target.is_nominal_influenced(5));
    }

    #[test]
    fn nominal_dependent_hash_prepends_linker_heads() {
        let mut hash = SaturationNominalDependentNodeHash::new(INVALID);
        let first = SaturationNominalDependentNodeDataId::new(1);
        let second = SaturationNominalDependentNodeDataId::new(2);

        assert_eq!(
            hash.add_nominal_dependent_node_data(9, first),
            SaturationNominalDependentNodeDataId::NONE
        );
        assert_eq!(hash.add_nominal_dependent_node_data(9, second), first);
        assert_eq!(hash.get_nominal_dependent_node_data(9), second);
        assert_eq!(
            hash.get_nominal_dependent_node_data(10),
            SaturationNominalDependentNodeDataId::NONE
        );
    }

    #[test]
    fn nominal_dependent_data_stores_node_type_and_next() {
        let mut data = SaturationNominalDependentNodeData::new(INVALID);
        let next = SaturationNominalDependentNodeDataId::new(4);

        data.init_nominal_dependent_node_data(
            SatNodeId::new(7),
            SaturationNominalConnectionType::NominalConnection,
        )
        .append(next);

        assert_eq!(
            data.get_dependent_individual_saturation_node(),
            SatNodeId::new(7)
        );
        assert_eq!(
            data.get_nominal_connection_type(),
            SaturationNominalConnectionType::NominalConnection
        );
        assert_eq!(data.get_next_nominal_connection_type_data(), next);
    }
}
