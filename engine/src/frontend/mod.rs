//! OWL functional-syntax (`.ofn`) normalisation frontend.
//!
//! Rust port of `engine/py/frontend.py` + `moose.sroiq.normalisation` +
//! `engine/py/preprocess.py`. Produces the engine JSON clause set
//! (`ofn_to_clauses`) that is structurally equivalent (modulo internal-symbol
//! renaming) to `frontend.ofn_to_clauses`, plus the `iri_map` / `named` /
//! `declared` side outputs that drive `owl_classify`'s output mapping.

pub mod clauses;
pub mod iri;
pub mod normalise;
pub mod parse;
pub mod preprocess;
pub mod rbox;
pub mod sexpr;
pub mod syntax;

use std::collections::BTreeSet;

use clauses::{clause, clause_to_json, Atom, DLClause, Term};
use iri::IriRegistry;

/// Result of `ofn_to_clauses`: the JSON clause set plus the output-mapping
/// side data.
pub struct FrontendResult {
    pub clauses: Vec<crate::json_io::JClause>,
    /// engine-internal short name -> full IRI (port of `full_iri`'s `_short_owner`).
    pub iri_map: std::collections::BTreeMap<String, String>,
    /// internal names backed by a real IRI (port of `is_named_iri`).
    pub named: Vec<String>,
    /// short names of every `Declaration(Class(...))`.
    pub declared: Vec<String>,
    /// whether the RBox is safe for the EL completion reasoner (port of
    /// `el_route.rbox_el_safe`); lets `owl_classify` route without re-parsing.
    pub el_rbox_safe: bool,
}

/// Concept names appearing (body or head) in a list of JSON clauses. Port of
/// `frontend._concept_names_in`.
fn concept_names_in(clauses: &[crate::json_io::JClause]) -> BTreeSet<String> {
    use crate::json_io::JAtom;
    let mut names = BTreeSet::new();
    for c in clauses {
        for atom in c.body.iter().chain(c.head.iter()) {
            if let JAtom::Concept { concept, .. } = atom {
                names.insert(concept.clone());
            }
        }
    }
    names
}

/// Port of `frontend.ofn_to_clauses` + the `iri_map`/`named`/`declared` outputs.
pub fn ofn_to_clauses(text: &str) -> Result<FrontendResult, parse::OutOfFragment> {
    let mut reg = IriRegistry::new();
    let (ontology, onto_nodes) = parse::parse_ontology(&mut reg, text)?;
    let (tbox, abox, hooks) = normalise::normalise(&ontology);
    let mut tbox = preprocess::augment(tbox, &abox, &hooks);

    // domain/range Horn clauses from the RBox records.
    let rbox = rbox::ofn_rbox(&mut reg, &onto_nodes);
    let el_rbox_safe = rbox::el_rbox_safe(&rbox);
    tbox.extend(preprocess::domain_range_clauses(&rbox));

    let mut jclauses: Vec<crate::json_io::JClause> =
        tbox.iter().map(clause_to_json).collect();

    // Seed every declared class absent from the clause set with a tautological
    // self-clause A(x) → A(x) (port of the declared-classes loop).
    let mut present = concept_names_in(&jclauses);
    let declared = parse::declared_classes(&mut reg, &onto_nodes);
    for name in &declared {
        if !present.contains(name) {
            present.insert(name.clone());
            let atom = Atom::Concept(name.clone(), Term::Var("x".to_string()));
            let self_cl: DLClause = clause([atom.clone()], [atom]);
            jclauses.push(clause_to_json(&self_cl));
        }
    }

    // iri_map / named: every internal name registered to a real IRI.
    let mut iri_map = std::collections::BTreeMap::new();
    let mut named = Vec::new();
    for internal in reg.owned_names() {
        iri_map.insert(internal.clone(), reg.full_iri(&internal));
        named.push(internal);
    }
    named.sort();

    Ok(FrontendResult {
        clauses: jclauses,
        iri_map,
        named,
        declared,
        el_rbox_safe,
    })
}
