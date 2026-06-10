//! OWL functional-syntax (`.ofn`) normalisation frontend.
//!
//! Rust port of `engine/py/frontend.py` + `moose.sroiq.normalisation` +
//! `engine/py/preprocess.py`. Produces the engine JSON clause set
//! (`ofn_to_clauses`) that is structurally equivalent (modulo internal-symbol
//! renaming) to `frontend.ofn_to_clauses`, plus the `iri_map` / `named` /
//! `declared` side outputs that drive `owl_classify`'s output mapping.

pub mod abox_consistency;
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
    /// the ABox forces an individual into two disjoint named classes, so the
    /// ontology is inconsistent (see `abox_consistency`). The CB engine drops
    /// ABox clauses and would miss this, so `owl_classify` short-circuits to an
    /// inconsistent result when set.
    pub abox_inconsistent: bool,
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

/// Per-stage wall timing, written to stderr when `KM_OFN_TIMING` is set. Cheap
/// (one `Instant::now()` per stage) and off by default, so the normal path is
/// unaffected.
struct StageTimer {
    on: bool,
    last: std::time::Instant,
}
impl StageTimer {
    fn new() -> Self {
        StageTimer {
            on: std::env::var_os("KM_OFN_TIMING").is_some(),
            last: std::time::Instant::now(),
        }
    }
    fn lap(&mut self, label: &str) {
        if self.on {
            let now = std::time::Instant::now();
            eprintln!(
                "[ofn-timing] {:<22} {:>8.3}s  rss={}MB hwm={}MB",
                label,
                (now - self.last).as_secs_f64(),
                read_status_mb("VmRSS:"),
                read_status_mb("VmHWM:")
            );
            self.last = now;
        }
    }
}

/// Read a `/proc/self/status` field in MB (0 if unavailable, e.g. non-Linux).
fn read_status_mb(field: &str) -> u64 {
    std::fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|s| {
            s.lines().find(|l| l.starts_with(field)).and_then(|l| {
                l.split_whitespace()
                    .nth(1)
                    .and_then(|v| v.parse::<u64>().ok())
            })
        })
        .map(|kb| kb / 1024)
        .unwrap_or(0)
}

/// Port of `frontend.ofn_to_clauses` + the `iri_map`/`named`/`declared` outputs.
pub fn ofn_to_clauses(text: &str) -> Result<FrontendResult, parse::OutOfFragment> {
    let mut t = StageTimer::new();
    let mut reg = IriRegistry::new();
    // Pass 1: stream the document into SROIQ axioms. No token vector and no
    // document AST is ever materialised (both used to be O(document) with a
    // heap string per token, and the AST was additionally deep-cloned for the
    // rbox/declared scans — together the 20 GB peak on 500 MB ontologies).
    let ontology = parse::parse_axioms(&mut reg, text)?;
    t.lap("parse+axioms");
    let (tbox, abox, hooks) = normalise::normalise(&ontology);
    // Project the named-class ABox-consistency data before the AST is dropped
    // (cheap: `None` unless the ontology has named-class disjointness). The
    // clash check is finished after the RBox domain/range records are built.
    let abox_data = abox_consistency::collect(&ontology);
    drop(ontology); // the syntax AST is dead once clausified
    t.lap("normalise");
    let mut tbox = preprocess::augment(tbox, &abox, &hooks);
    // Inverse-role bridge clauses (swapped-orientation role heads) are not EL;
    // elc's screen rejects them, but route past it up front. The rbox-record
    // check below misses bare `ObjectInverseOf` in concepts (no rbox record),
    // so this flag is the authoritative one.
    let has_inverse = !hooks.role_inverses.is_empty();
    drop(abox);
    drop(hooks);
    t.lap("augment");

    // Pass 2: re-stream the (cheap, zero-copy) parse for the RBox records and
    // the declared-class list. Re-parsing trades a few seconds of tokenising
    // for not retaining the document AST across `normalise`/`augment`. The
    // `reg.short` call order — all axiom names, then all rbox names, then all
    // declared names — matches the old single-parse code exactly, so the
    // assigned internal names are identical.
    let mut rbox: Vec<rbox::RboxRecord> = Vec::new();
    let mut declared_raw: Vec<&str> = Vec::new();
    parse::for_each_ontology_child(text, |node| {
        rbox::rbox_node(&mut reg, node, &mut rbox);
        if let Some(name) = parse::declared_class_node(node) {
            declared_raw.push(name);
        }
        Ok(())
    })?;
    let el_rbox_safe = rbox::el_rbox_safe(&rbox) && !has_inverse;
    let abox_inconsistent = abox_data
        .map(|d| d.is_inconsistent(&rbox))
        .unwrap_or(false);
    tbox.extend(preprocess::domain_range_clauses(&rbox));
    let mut declared = Vec::new();
    for name in declared_raw {
        let s = reg.short(name);
        if s != "owl:Thing" && s != "owl:Nothing" {
            declared.push(s);
        }
    }
    t.lap("rbox+domain+declared");

    // Consume `tbox` while converting, so the DLClause set is freed as the JSON
    // clause set is built (rather than holding both in full at once).
    let mut jclauses: Vec<crate::json_io::JClause> =
        tbox.into_iter().map(|c| clause_to_json(&c)).collect();
    t.lap("clause_to_json");

    // Seed every declared class absent from the clause set with a tautological
    // self-clause A(x) → A(x) (port of the declared-classes loop).
    let mut present = concept_names_in(&jclauses);
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
    t.lap("declared_seed+iri_map");

    Ok(FrontendResult {
        clauses: jclauses,
        iri_map,
        named,
        declared,
        el_rbox_safe,
        abox_inconsistent,
    })
}
