//! Port of `Reasoner/Ontology/CRoleChain.{h,cpp}` — a role chain
//! `R1 ∘ R2 ∘ … ∘ Rn ⊑ S` as the ordered role list plus its reversed
//! inverse-role list (built lazily by the role-chain automata preprocessor's
//! `createInverseRoleChainLinkers`).
//!
//! KONCLUDE-PORT-NOTE[api]: `CRoleChain : CTagItem` carries its tag inline
//! (`mTag` via `CTagItem`); linkers (`CXLinker<CRole*>*`) map to `Vec<RoleId>`
//! per the module convention (see `role.rs`), with `append*` = push and
//! `prepend*` = front-insert so the preprocessor's reversed-list construction
//! (`prependInverseRoleChainLinker` in a forward walk) stays order-exact.

#![allow(dead_code)]

use super::stubs::TerminologyId;
use super::substrate::{Cint64, Id};
use super::RoleId;

/// Port of `CRoleChain`.
pub struct RoleChain {
    /// Port of `CTagItem::mTag` as reached through `getRoleChainTag`.
    pub role_chain_tag: Cint64,
    /// Port of `CRoleChain::mTerm`.
    pub terminology: Option<TerminologyId>,
    /// Port of `CRoleChain::mRoleChainLinker` (`CXLinker<CRole*>*`).
    pub role_chain_linker: Vec<RoleId>,
    /// Port of `CRoleChain::mInverseRoleChainLinker` (`CXLinker<CRole*>*`).
    pub inverse_role_chain_linker: Vec<RoleId>,
}

/// `CRoleChain*` → `RoleChainId`.
pub type RoleChainId = Id<RoleChain>;

impl RoleChain {
    /// Port of `CRoleChain::CRoleChain` + `initRoleChain`.
    pub fn new() -> Self {
        RoleChain {
            role_chain_tag: 0,
            terminology: None,
            role_chain_linker: Vec::new(),
            inverse_role_chain_linker: Vec::new(),
        }
    }

    /// Port of `CRoleChain::initRoleChain`.
    pub fn init_role_chain(&mut self) -> &mut Self {
        self.role_chain_tag = 0;
        self.terminology = None;
        self.role_chain_linker.clear();
        self.inverse_role_chain_linker.clear();
        self
    }

    /// Port of `CRoleChain::setRoleChainTag`.
    pub fn set_role_chain_tag(&mut self, role_chain_tag: Cint64) -> &mut Self {
        self.role_chain_tag = role_chain_tag;
        self
    }

    /// Port of `CRoleChain::getRoleChainTag`.
    pub fn get_role_chain_tag(&self) -> Cint64 {
        self.role_chain_tag
    }

    /// Port of `CRoleChain::setTerminology`.
    pub fn set_terminology(&mut self, terminology: Option<TerminologyId>) -> &mut Self {
        self.terminology = terminology;
        self
    }

    /// Port of `CRoleChain::getTerminology`.
    pub fn get_terminology(&self) -> Option<TerminologyId> {
        self.terminology
    }

    /// Port of `CRoleChain::getRoleChainLinker`.
    pub fn get_role_chain_linker(&self) -> &[RoleId] {
        &self.role_chain_linker
    }

    /// Port of `CRoleChain::appendRoleChainLinker`.
    pub fn append_role_chain_linker(&mut self, role: RoleId) -> &mut Self {
        self.role_chain_linker.push(role);
        self
    }

    /// Port of `CRoleChain::prependRoleChainLinker`.
    pub fn prepend_role_chain_linker(&mut self, role: RoleId) -> &mut Self {
        self.role_chain_linker.insert(0, role);
        self
    }

    /// Port of `CRoleChain::setRoleChainLinker`.
    pub fn set_role_chain_linker(&mut self, roles: Vec<RoleId>) -> &mut Self {
        self.role_chain_linker = roles;
        self
    }

    /// Port of `CRoleChain::getInverseRoleChainLinker`.
    pub fn get_inverse_role_chain_linker(&self) -> &[RoleId] {
        &self.inverse_role_chain_linker
    }

    /// `getInverseRoleChainLinker()` used as the "has it been built?" test
    /// (`if (!roleChain->getInverseRoleChainLinker())` in
    /// `createInverseRoleChainLinkers` / `collectSubRoleChains`).
    pub fn has_inverse_role_chain_linker(&self) -> bool {
        !self.inverse_role_chain_linker.is_empty()
    }

    /// Port of `CRoleChain::appendInverseRoleChainLinker`.
    pub fn append_inverse_role_chain_linker(&mut self, role: RoleId) -> &mut Self {
        self.inverse_role_chain_linker.push(role);
        self
    }

    /// Port of `CRoleChain::prependInverseRoleChainLinker`.
    pub fn prepend_inverse_role_chain_linker(&mut self, role: RoleId) -> &mut Self {
        self.inverse_role_chain_linker.insert(0, role);
        self
    }

    /// Port of `CRoleChain::setInverseRoleChainLinker`.
    pub fn set_inverse_role_chain_linker(&mut self, roles: Vec<RoleId>) -> &mut Self {
        self.inverse_role_chain_linker = roles;
        self
    }
}

impl Default for RoleChain {
    fn default() -> Self {
        RoleChain::new()
    }
}
