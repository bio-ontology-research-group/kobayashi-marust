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
use super::individual::{Individual, Variable};
use super::role::Role;
use super::substrate::Arena;
use super::{ConceptId, IndividualId, RoleId, VariableId};

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
    /// `CRole` pool (the static role / RBox terminology).
    roles: Arena<Role>,
    /// `CIndividual` pool (the static individuals).
    individuals: Arena<Individual>,
    /// `CVariable` pool (the static rule variables).
    variables: Arena<Variable>,
}

impl OntologyArenas {
    pub fn new() -> Self {
        OntologyArenas {
            concepts: Arena::new(),
            roles: Arena::new(),
            individuals: Arena::new(),
            variables: Arena::new(),
        }
    }

    onto_accessors!(concepts, Concept, ConceptId, concept, concept_mut, alloc_concept);
    onto_accessors!(roles, Role, RoleId, role, role_mut, alloc_role);
    onto_accessors!(
        individuals,
        Individual,
        IndividualId,
        individual,
        individual_mut,
        alloc_individual
    );
    onto_accessors!(
        variables,
        Variable,
        VariableId,
        variable,
        variable_mut,
        alloc_variable
    );
}

impl Default for OntologyArenas {
    fn default() -> Self {
        Self::new()
    }
}
