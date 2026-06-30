//! `model` — the static ontology layer of the port: the concept/role/individual
//! types the completion engine reads (Konclude `Source/Reasoner/Ontology/`).
//!
//! Canonical typed-id aliases live here so every ported file refers to the same
//! names. Rust type names drop the Konclude `C` prefix (the original is recorded
//! in each item's doc-comment, e.g. `/// Port of `CConcept`.`).

pub mod substrate;
pub mod stubs;     // W1: not-yet-ported placeholder ids (CRoleChain/CRoleData/CTerminology/CName)
pub mod op;        // W1: operator codes (CCxxx) + CConceptOperator flag groups
pub mod concept;   // W1: CConcept
pub mod role;      // W1: CRole
pub mod individual; // W1: CIndividual + CVariable
pub mod ontology;   // W3.5: OntologyArenas — the static read-shared terminology (CConcept/CRole/CIndividual/CVariable)

pub use substrate::{Arena, Cint64, Id, NegLink, Trail, INVALID};
pub use stubs::{NameId, RoleChainId, RoleDataId, TerminologyId};

/// `CConcept*`  → `ConceptId`.
pub type ConceptId = Id<concept::Concept>;
/// `CRole*`     → `RoleId`.
pub type RoleId = Id<role::Role>;
/// `CIndividual*` → `IndividualId`.
pub type IndividualId = Id<individual::Individual>;
/// `CVariable*` → `VariableId`.
pub type VariableId = Id<individual::Variable>;
