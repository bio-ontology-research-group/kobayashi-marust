//! `process::sat_node_vector` — `CIndividualSaturationProcessNodeVector`.
//!
//! Konclude's class is a thin `CDefaultDynamicReferenceVectorBase` specialization
//! over `CIndividualSaturationProcessNode*`. The Rust port stores `SatNodeId`
//! slots directly and preserves the non-negative dynamic-vector indexing.

#![allow(dead_code)]

use super::super::model::substrate::Cint64;
use super::SatNodeId;

/// Port of `CIndividualSaturationProcessNodeVector`.
///
/// KONCLUDE-PORT-NOTE[ownership]: `CIndividualSaturationProcessNode*` becomes a
/// `SatNodeId` into `ProcessContext::sat_nodes`; `Id::NONE` is the C++ `nullptr`.
/// Unlike `CIndividualProcessNodeVector`, this is not a double-dynamic vector:
/// saturation-resolved individual ids are non-negative and index a single vector.
#[derive(Debug, Clone, Default)]
pub struct IndividualSaturationProcessNodeVector {
    slots: Vec<SatNodeId>,
}

impl IndividualSaturationProcessNodeVector {
    /// Port of `CIndividualSaturationProcessNodeVector::CIndividualSaturationProcessNodeVector`.
    pub fn new() -> Self {
        Self { slots: Vec::new() }
    }

    #[inline]
    fn index(id: Cint64) -> Option<usize> {
        if id >= 0 {
            Some(id as usize)
        } else {
            None
        }
    }

    /// Port of `CDefaultDynamicReferenceVectorBase::getData`.
    pub fn get_data(&self, id: Cint64) -> SatNodeId {
        Self::index(id)
            .and_then(|idx| self.slots.get(idx).copied())
            .unwrap_or(SatNodeId::NONE)
    }

    /// Port of `CDefaultDynamicReferenceVectorBase::hasData`.
    pub fn has_data(&self, id: Cint64) -> bool {
        self.get_data(id).is_some()
    }

    /// Port of `CDefaultDynamicReferenceVectorBase::setLocalData`.
    pub fn set_local_data(&mut self, id: Cint64, node: SatNodeId) -> &mut Self {
        if let Some(idx) = Self::index(id) {
            if idx >= self.slots.len() {
                self.slots.resize(idx + 1, SatNodeId::NONE);
            }
            self.slots[idx] = node;
        }
        self
    }

    /// Port of `CDefaultDynamicReferenceVectorBase::setData`.
    pub fn set_data(&mut self, id: Cint64, node: SatNodeId) -> &mut Self {
        self.set_local_data(id, node)
    }

    /// Port of `CDynamicReferenceVectorBase::getItemCount`.
    pub fn get_item_count(&self) -> Cint64 {
        self.slots.len() as Cint64
    }

    /// Port of `CDynamicReferenceVectorBase::getItemMaxIndex`.
    pub fn get_item_max_index(&self) -> Cint64 {
        self.slots.len() as Cint64 - 1
    }

    /// Port-facing equivalent of `referenceVector` for the currently needed
    /// parent-child handoff shape.
    pub fn reference_vector(&mut self, other: &IndividualSaturationProcessNodeVector) -> &mut Self {
        *self = other.clone();
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sat_vector_sparse_set_data_sets_item_count_to_max_index_plus_one() {
        let mut vec = IndividualSaturationProcessNodeVector::new();
        let node = SatNodeId::new(3);

        vec.set_data(7, node);

        assert_eq!(vec.get_data(7), node);
        assert_eq!(vec.get_data(6), SatNodeId::NONE);
        assert_eq!(vec.get_item_count(), 8);
        assert_eq!(vec.get_item_max_index(), 7);
    }

    #[test]
    fn sat_vector_negative_ids_are_outside_the_dynamic_vector() {
        let mut vec = IndividualSaturationProcessNodeVector::new();
        vec.set_data(-1, SatNodeId::new(1));

        assert_eq!(vec.get_data(-1), SatNodeId::NONE);
        assert_eq!(vec.get_item_count(), 0);
        assert_eq!(vec.get_item_max_index(), -1);
    }
}
