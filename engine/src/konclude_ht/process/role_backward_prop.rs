//! Ordinary role-backward-propagation substrate.
//!
//! Direct port of Konclude:
//! - `CBackwardPropagationLink`
//! - `CBackwardPropagationReapplyDescriptor`
//! - `CRoleBackwardPropagationHashData`
//! - `CRoleBackwardPropagationHash`

#![allow(dead_code)]

use std::collections::HashMap;

use super::super::model::substrate::{Cint64, Id};
use super::super::model::{RoleId, INVALID};
use super::{ConDescId, NodeId};

/// `CBackwardPropagationLink*`.
pub type BackwardPropagationLinkId = Id<BackwardPropagationLink>;
/// `CBackwardPropagationReapplyDescriptor*`.
pub type BackwardPropagationReapplyDescriptorId = Id<BackwardPropagationReapplyDescriptor>;
/// `CRoleBackwardPropagationHash*`.
pub type RoleBackwardPropagationHashId = Id<RoleBackwardPropagationHash>;

/// Port of `CBackwardPropagationLink`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BackwardPropagationLink {
    /// `CRole* mRole`.
    pub role: RoleId,
    /// `CIndividualProcessNode* mSourceIndividual`.
    pub source_individual: NodeId,
    /// `CLinkerBase` next pointer.
    pub next: BackwardPropagationLinkId,
}

impl Default for BackwardPropagationLink {
    fn default() -> Self {
        Self::new()
    }
}

impl BackwardPropagationLink {
    /// Port of `CBackwardPropagationLink::CBackwardPropagationLink`.
    pub fn new() -> Self {
        Self {
            role: RoleId::NONE,
            source_individual: NodeId::NONE,
            next: BackwardPropagationLinkId::NONE,
        }
    }

    /// Port of `CBackwardPropagationLink::initBackwardPropagationLink`.
    pub fn init_backward_propagation_link(
        &mut self,
        source_individual: NodeId,
        role: RoleId,
    ) -> &mut Self {
        self.role = role;
        self.source_individual = source_individual;
        self
    }

    /// Port of `CBackwardPropagationLink::getLinkRole`.
    pub fn get_link_role(&self) -> RoleId {
        self.role
    }

    /// Port of `CBackwardPropagationLink::setLinkRole`.
    pub fn set_link_role(&mut self, role: RoleId) -> &mut Self {
        self.role = role;
        self
    }

    /// Port of `CBackwardPropagationLink::getSourceIndividual`.
    pub fn get_source_individual(&self) -> NodeId {
        self.source_individual
    }

    /// Port of `CLinkerBase::getNext`.
    pub fn get_next(&self) -> BackwardPropagationLinkId {
        self.next
    }

    /// Port of `CLinkerBase::setNext`.
    pub fn set_next(&mut self, next: BackwardPropagationLinkId) -> &mut Self {
        self.next = next;
        self
    }
}

/// Port of `CBackwardPropagationReapplyDescriptor`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BackwardPropagationReapplyDescriptor {
    /// `CConceptDescriptor* mReapplyConDes`.
    pub reapply_con_des: ConDescId,
    /// `CLinkerBase` next pointer.
    pub next: BackwardPropagationReapplyDescriptorId,
}

impl Default for BackwardPropagationReapplyDescriptor {
    fn default() -> Self {
        Self::new()
    }
}

impl BackwardPropagationReapplyDescriptor {
    /// Port of `CBackwardPropagationReapplyDescriptor::CBackwardPropagationReapplyDescriptor`.
    pub fn new() -> Self {
        Self {
            reapply_con_des: ConDescId::NONE,
            next: BackwardPropagationReapplyDescriptorId::NONE,
        }
    }

    /// Port of `CBackwardPropagationReapplyDescriptor::initBackwardPropagationReapplyDescriptor`.
    pub fn init_backward_propagation_reapply_descriptor(
        &mut self,
        con_des: ConDescId,
    ) -> &mut Self {
        self.reapply_con_des = con_des;
        self
    }

    /// Port of `CBackwardPropagationReapplyDescriptor::getReapllyConceptDescriptor`.
    pub fn get_reaplly_concept_descriptor(&self) -> ConDescId {
        self.reapply_con_des
    }

    /// Port of `CLinkerBase::getNext`.
    pub fn get_next(&self) -> BackwardPropagationReapplyDescriptorId {
        self.next
    }

    /// Port of `CLinkerBase::setNext`.
    pub fn set_next(&mut self, next: BackwardPropagationReapplyDescriptorId) -> &mut Self {
        self.next = next;
        self
    }
}

/// Port of `CRoleBackwardPropagationHashData`.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct RoleBackwardPropagationHashData {
    /// `CBackwardPropagationLink* mLinkLinker`.
    pub link_linker: BackwardPropagationLinkId,
    /// `CBackwardPropagationReapplyDescriptor* mReapplyLinker`.
    pub reapply_linker: BackwardPropagationReapplyDescriptorId,
}

impl Default for RoleBackwardPropagationHashData {
    fn default() -> Self {
        Self::new()
    }
}

impl RoleBackwardPropagationHashData {
    /// Port of `CRoleBackwardPropagationHashData::CRoleBackwardPropagationHashData`.
    pub fn new() -> Self {
        Self {
            link_linker: BackwardPropagationLinkId::NONE,
            reapply_linker: BackwardPropagationReapplyDescriptorId::NONE,
        }
    }
}

/// Port of `CRoleBackwardPropagationHash`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RoleBackwardPropagationHash {
    /// `CProcessContext* mContext` (opaque in the arena port).
    pub context: Cint64,
    /// `CPROCESSHASH<CRole*, CRoleBackwardPropagationHashData>`.
    pub role_back_prop_data_hash: HashMap<RoleId, RoleBackwardPropagationHashData>,
}

impl Default for RoleBackwardPropagationHash {
    fn default() -> Self {
        Self::new(INVALID)
    }
}

impl RoleBackwardPropagationHash {
    /// Port of `CRoleBackwardPropagationHash::CRoleBackwardPropagationHash`.
    pub fn new(context: Cint64) -> Self {
        Self {
            context,
            role_back_prop_data_hash: HashMap::new(),
        }
    }

    /// Port of `CRoleBackwardPropagationHash::getRoleBackwardPropagationDataHash`.
    pub fn get_role_backward_propagation_data_hash(
        &self,
    ) -> &HashMap<RoleId, RoleBackwardPropagationHashData> {
        &self.role_back_prop_data_hash
    }

    /// Mutable arena-port counterpart of `getRoleBackwardPropagationDataHash`.
    pub fn get_role_backward_propagation_data_hash_mut(
        &mut self,
    ) -> &mut HashMap<RoleId, RoleBackwardPropagationHashData> {
        &mut self.role_back_prop_data_hash
    }
}
