//! OWL functional-syntax (`.ofn`) normalisation frontend.
//!
//! Rust port of `engine/py/frontend.py` + `moose.sroiq.normalisation` +
//! `engine/py/preprocess.py`. Produces the engine JSON clause set
//! (`ofn_to_clauses`) that is structurally equivalent (modulo internal-symbol
//! renaming) to `frontend.ofn_to_clauses`, plus the `iri_map` / `named` /
//! `declared` side outputs that drive `owl_classify`'s output mapping.

pub mod abox_consistency;
pub mod clauses;
pub mod data_abox;
pub mod data_range;
pub mod datatypes;
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
    /// named classes provably containing at least one asserted individual
    /// (direct `ClassAssertion` plus domain/range typing of asserted roles).
    /// If classification later proves such a class unsatisfiable, the ontology
    /// is inconsistent; `owl_classify` applies that rule after the engine runs.
    pub asserted_classes: Vec<String>,
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
    let (tbox, abox, mut hooks) = normalise::normalise(&ontology);
    // Project the named-class ABox-consistency data before the AST is dropped
    // (cheap: `None` unless the ontology has named-class disjointness). The
    // clash check is finished after the RBox domain/range records are built.
    let abox_data = abox_consistency::collect(&ontology);
    let (asserted_direct, asserted_roles) = abox_consistency::asserted_profile(&ontology);
    drop(ontology); // the syntax AST is dead once clausified
    t.lap("normalise");
    // Under KM_NOMINALS the ground ABox + nominal defining clauses enter the
    // clause set (docs/NOMINALS-CB.md Phase 0); those are not EL, so fence the
    // ontology off the elc path up front.
    let nominals_mode = std::env::var_os("KM_NOMINALS").is_some();
    let has_individuals = !abox.is_empty() || !hooks.nominal_to_individual.is_empty();
    let (mut tbox, chain_info) = preprocess::augment_with_chains(tbox, &abox, &hooks);
    // Inverse-role bridge clauses (swapped-orientation role heads) are not EL;
    // elc's screen rejects them, but route past it up front. The rbox-record
    // check below misses bare `ObjectInverseOf` in concepts (no rbox record),
    // so this flag is the authoritative one.
    let role_inverses = std::mem::take(&mut hooks.role_inverses);
    let symmetric_roles = std::mem::take(&mut hooks.symmetric_roles);
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
    let mut data_ranges = data_range::DataRanges::default();
    let mut data_abox = data_abox::DataAbox::default();
    parse::for_each_ontology_child(text, |node| {
        rbox::rbox_node(&mut reg, node, &mut rbox);
        data_ranges.observe(node);
        data_abox.observe(node);
        if let Some(name) = parse::declared_class_node(node) {
            declared_raw.push(name);
        }
        Ok(())
    })?;
    // asserted-ABox inconsistency: named-disjointness clash (abox_consistency)
    // or datatype range/functionality clash (data_abox); both sound prechecks.
    let abox_inconsistent = abox_data
        .map(|d| d.is_inconsistent(&rbox))
        .unwrap_or(false)
        || data_abox.is_inconsistent();
    // named classes with a provable asserted member: direct assertions plus
    // domain/range typing of asserted roles (`R(a,b)` + `Domain(R,C)` => `a:C`).
    let mut asserted_classes: BTreeSet<String> = asserted_direct;
    for r in &rbox {
        match r {
            rbox::RboxRecord::Domain(p, d) if asserted_roles.contains(p) => {
                asserted_classes.insert(d.clone());
            }
            rbox::RboxRecord::Range(p, c) if asserted_roles.contains(p) => {
                asserted_classes.insert(c.clone());
            }
            _ => {}
        }
    }
    let domain_range = preprocess::domain_range_clauses(&rbox);
    // Chain / transitivity recognition for pure-domain consumers of chain
    // targets (e.g. `R∘S⊑T, domain(T)=D`): these consumers only exist now, so
    // `augment`'s pass-1 chain/transitivity encodings missed them. Additive
    // and sound (fresh recognition clauses only); required for completeness
    // (ore_ont_11745's unsat detection). DEFAULT ON since the full-corpus
    // validation sweep (5976: 0 unsound, 0 incomplete vs gold modulo the
    // datatype gap); KM_NO_CHAIN_DOMAIN restores the prior output for A/B
    // debugging. Cost: chain-heavy ontologies (2313, 8737) can run past the
    // benchmark budget — honest resource limits, never silent approximation.
    // Run before extending so the recognitions see the same `domain_range` set.
    if std::env::var_os("KM_NO_CHAIN_DOMAIN").is_none() {
        tbox.extend(preprocess::domain_consumer_chain_clauses(&chain_info, &domain_range));
    }
    tbox.extend(domain_range);
    // All consumers are in place (augment encodings + domain/range), so dead
    // inverse bridges can be identified and dropped.
    let no_prune = std::env::var_os("KM_NO_PRUNE").is_some();
    if !no_prune {
        preprocess::prune_dead_inverse_bridges(&mut tbox, &role_inverses);
    }
    // Decide EL routing on the full clause set. An ontology fenced out of the EL
    // fast path only by symmetric / inverse roles is still EL-routable when
    // those roles are inert -- not in the backward slice of roles that can reach
    // a named-class subsumption, equality, or unsat (`concept_relevant_roles`).
    // Prune the inert reverse-edge clauses and relax the routing predicate; roles
    // in the slice keep the ontology on the CB engine.
    let relevant = preprocess::concept_relevant_roles(&tbox);
    if !no_prune {
        preprocess::prune_inert_role_bridges(&mut tbox, &symmetric_roles, &role_inverses, &relevant);
    }
    let inverses_inert = role_inverses
        .iter()
        .all(|(r, s)| !relevant.contains(r) && !relevant.contains(s));
    let el_rbox_safe = rbox::el_rbox_safe_relaxed(&rbox, &relevant)
        && inverses_inert
        && !(nominals_mode && has_individuals);
    t.lap("relevance+prune");
    let mut declared = Vec::new();
    for name in declared_raw {
        let s = reg.short(name);
        if s != "owl:Thing" && s != "owl:Nothing" {
            declared.push(s);
        }
    }
    // A data property whose `DataPropertyRange` axioms intersect to the empty
    // set can carry no value: emit `P(x,y) -> ⊥` so any class requiring a
    // P-value is unsatisfiable (ore_ont_7901's structureFormat). Resolved last,
    // after declared names, to leave the internal-name order unchanged for
    // ontologies with no empty range.
    tbox.extend(data_ranges.empty_range_constraints(&mut reg));
    // Datatype (concrete-domain) relations between the `__dt__` abstraction
    // concepts occurring in the clause set: membership, value (in)equality,
    // range subsumption/disjointness, and finite covers, decided per the
    // OWL 2 datatype map and emitted as ordinary clauses (unknown relations
    // emit nothing, so unsupported corners keep the old sound abstraction).
    // KM_NO_DATATYPES restores the bare abstraction for A/B debugging.
    if std::env::var_os("KM_NO_DATATYPES").is_none() {
        let mut dt_names: BTreeSet<String> = BTreeSet::new();
        for c in &tbox {
            for a in c.body.iter().chain(c.head.iter()) {
                if let Atom::Concept(name, _) = a {
                    if name.starts_with("__dt__") {
                        dt_names.insert(name.clone());
                    }
                }
            }
        }
        if !dt_names.is_empty() {
            tbox.extend(datatypes::datatype_relation_clauses(&dt_names, 8));
        }
    }
    t.lap("rbox+domain+declared");

    // KM_EMELIM: complementary-definer excluded-middle elimination (B≡¬A) — the
    // CB analogue of the HT-path absorption. Removes the ⊤⊑A∨B disjunctive facts
    // that otherwise produce covering disjuncts on every individual. Gated;
    // default off ⇒ output byte-identical to the prior binary.
    let tbox = if std::env::var_os("KM_EMELIM").is_some() {
        let (t, n) = clauses::elim_complements(tbox);
        if std::env::var_os("KM_OFN_TIMING").is_some() {
            eprintln!("ofn [emelim] eliminated {} complementary pairs", n);
        }
        t
    } else {
        tbox
    };

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
        asserted_classes: asserted_classes.into_iter().collect(),
    })
}
