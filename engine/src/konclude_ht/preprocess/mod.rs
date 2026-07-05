//! `preprocess` — ports of `Reasoner/Preprocess/*` (the ontology-rewriting
//! passes that run between build and calculation).
//!
//! First unit: `CRoleChainAutomataTransformationPreProcess` — compiles
//! transitive roles / role chains / the sub-role hierarchy into role-automaton
//! state + transition concepts (`CCAQCHOOCE` / `CCAQALL` / `CCAQAND`), the
//! producer for the already-ported automat choose/AND rules in
//! `completion/u05.rs`.

pub mod role_chain_automata;

#[cfg(test)]
mod automata_test;
