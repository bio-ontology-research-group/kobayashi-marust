//! `model::stubs` — shared not-yet-ported ontology-model placeholder types.
//!
//! KONCLUDE-PORT-NOTE[api]: `CRoleChain`, `CRoleData`, `CTerminology`, and
//! `CName` are separate ontology-model units that land in later port units
//! (`Reasoner/Ontology/CRoleChain.{h,cpp}`, `CRoleData.{h,cpp}`,
//! `CTerminology.{h,cpp}`, `CName.{h,cpp}`). Until they exist, they are stubbed
//! here as placeholder arena objects so the using sites' fields/signatures stay
//! exact. These definitions are shared across `role.rs` (and later units) so they
//! live in one place rather than being defined inside any single ported file.

#![allow(dead_code)]

use super::substrate::{Cint64, Id};

// `CRoleChain` graduated from this stub file to the full port in
// `model/role_chain.rs` (with the role-chain automata preprocessor).

/// Port of `CRoleData` (placeholder; full port lands with `CRoleData.{h,cpp}`).
pub struct RoleData;
/// `CRoleData*` → `RoleDataId`.
pub type RoleDataId = Id<RoleData>;

/// Port of `CTerminology` (placeholder; full port lands with `CTerminology.{h,cpp}`).
/// Only the `getTerminologyID()` accessor that `CRole` reaches through is modelled.
pub struct Terminology {
    pub terminology_id: Cint64,
}
impl Terminology {
    /// Port of `CTerminology::getTerminologyID`.
    pub fn get_terminology_id(&self) -> Cint64 {
        self.terminology_id
    }
}
/// `CTerminology*` → `TerminologyId`.
pub type TerminologyId = Id<Terminology>;

/// Port of `CName` (placeholder; full port lands with `CName.{h,cpp}`).
pub struct Name;
/// `CName*` → `NameId`.
pub type NameId = Id<Name>;
