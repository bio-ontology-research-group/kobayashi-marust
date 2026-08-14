//! OWL functional-syntax (`.ofn`) normalisation frontend.
//!
//! Rust port of `engine/py/frontend.py` + `moose.sroiq.normalisation` +
//! `engine/py/preprocess.py`. Produces the engine JSON clause set
//! (`ofn_to_clauses`) that is structurally equivalent (modulo internal-symbol
//! renaming) to `frontend.ofn_to_clauses`, plus the `iri_map` / `named` /
//! `declared` side outputs that drive `owl_classify`'s output mapping.

pub mod abox_consistency;
pub mod bottom_prepass;
pub mod clauses;
pub mod data_abox;
pub mod data_range;
pub mod datatypes;
pub mod iri;
pub mod normalise;
pub mod parse;
pub mod preprocess;
pub mod profile;
pub mod rbox;
mod rule_certificate;
pub mod sexpr;
pub mod syntax;
pub mod top_role;

use std::collections::{BTreeMap, BTreeSet, HashSet, VecDeque};

use clauses::{clause, clause_to_json, Atom, DLClause, Term};
use iri::IriRegistry;

/// Result of `ofn_to_clauses`: the JSON clause set plus the output-mapping
/// side data.
pub struct FrontendResult {
    pub clauses: Vec<crate::json_io::JClause>,
    /// RBox side data retained for production role-automata construction.
    pub rbox: Vec<Vec<String>>,
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
    /// Exact nominal/ABox provenance for the native Konclude bridge. Empty on
    /// nominal-free inputs; `complete=false` makes the bridge fail closed.
    pub nominal_abox: crate::json_io::NominalAboxMeta,
    /// KM_HT_CARD: first-class qualified number restrictions (`define`'s `≥n`/`≤n`
    /// markers). Empty unless the frontend `KM_HT_CARD` flag is set.
    pub cardinalities: Vec<crate::json_io::CardMeta>,
    /// Fresh-concept structural provenance used by the triggered HT absorber.
    pub definers: Vec<crate::json_io::DefinerMeta>,
    /// Normalized source TBox used by pre-clausal triggered absorption.
    pub source_axioms: Vec<crate::json_io::SourceAxiomMeta>,
    /// KM_HT_RULES: parsed SWRL DL-safe rules, carried to `cb_to_ht`. Empty unless
    /// the frontend `KM_HT_RULES` flag is set (so the default output is unchanged).
    pub rules: Vec<crate::json_io::JRule>,
    /// Konclude-compatible expressivity plus source/clause statistics. Carried
    /// only in the split meta channel, never in the reasoner clause input.
    pub profile: profile::OntologyProfile,
    /// Procedure selected from the source profile and, for an ELC proposal,
    /// refined by the exact normalized-clause fragment gate (`manual` for a
    /// standalone frontend invocation).
    pub route: String,
}

/// Preserve every parsed object ABox assertion together with the exact nominal
/// proxies and class markers allocated by normalization.  This is deliberately
/// redundant: source expressions make the payload auditable, while normalized
/// marker names let the fast hypertableau seed the same class expressions
/// without reverse-engineering generated symbols.  Any mismatch fails closed.
fn collect_nominal_abox(
    ontology: &syntax::Ontology,
    abox: &[DLClause],
    hooks: &normalise::GroundHooks,
    source: &profile::SourceStatistics,
) -> crate::json_io::NominalAboxMeta {
    use crate::json_io::{NominalAboxMeta, NominalIndividualMeta, NominalRoleAssertionMeta};
    use syntax::Axiom;

    if source.abox_axioms == 0
        && hooks.nominal_to_individual.is_empty()
        && hooks.abox_nominal_to_individual.is_empty()
    {
        return NominalAboxMeta::default();
    }

    let mut by_individual: BTreeMap<String, NominalIndividualMeta> = BTreeMap::new();
    for (proxy, individual) in hooks
        .nominal_to_individual
        .iter()
        .chain(hooks.abox_nominal_to_individual.iter())
    {
        by_individual
            .entry(individual.clone())
            .or_insert_with(|| NominalIndividualMeta {
                individual: individual.clone(),
                ..NominalIndividualMeta::default()
            })
            .proxies
            .push(proxy.clone());
    }
    for entry in by_individual.values_mut() {
        entry.proxies.sort();
        entry.proxies.dedup();
    }

    // Normalization emits exactly one ground concept fact per source
    // ClassAssertion.  Keep its generated marker in per-individual source order.
    let mut marker_queue: BTreeMap<String, VecDeque<String>> = BTreeMap::new();
    for clause in abox {
        if !clause.body.is_empty() || clause.head.len() != 1 {
            continue;
        }
        if let Atom::Concept(marker, Term::Ind(individual)) = &clause.head[0] {
            marker_queue
                .entry(individual.clone())
                .or_default()
                .push_back(marker.clone());
        }
    }

    let mut different = BTreeSet::new();
    let mut same = BTreeSet::new();
    let mut role_assertions = BTreeSet::new();
    let mut negative_role_assertions = BTreeSet::new();
    let mut unsupported = BTreeSet::new();
    let mut parsed_class = 0u64;
    let mut parsed_role = 0u64;
    let mut parsed_negative_role = 0u64;
    let mut parsed_different_pairs = 0u64;
    let mut parsed_same_pairs = 0u64;

    fn require_individual(
        by_individual: &BTreeMap<String, NominalIndividualMeta>,
        unsupported: &mut BTreeSet<String>,
        individual: &str,
        context: &str,
    ) -> bool {
        if by_individual.contains_key(individual) {
            true
        } else {
            unsupported.insert(format!(
                "{context} individual {individual} has no normalizer nominal proxy"
            ));
            false
        }
    }

    for axiom in ontology.abox() {
        match axiom {
            Axiom::ConceptAssertion(concept, individual) => {
                parsed_class += 1;
                if !require_individual(
                    &by_individual,
                    &mut unsupported,
                    individual,
                    "ClassAssertion",
                ) {
                    continue;
                }
                let marker = marker_queue
                    .get_mut(individual)
                    .and_then(VecDeque::pop_front);
                match marker {
                    Some(marker) => {
                        let entry = by_individual.get_mut(individual).unwrap();
                        entry.assertions.push(normalise::nnf(concept));
                        entry.assertion_markers.push(marker);
                    }
                    None => {
                        unsupported.insert(format!(
                            "ClassAssertion({individual}) has no normalized marker"
                        ));
                    }
                }
            }
            Axiom::RoleAssertion(role, source, target) => {
                parsed_role += 1;
                if matches!(
                    role.as_str(),
                    "owl:topObjectProperty"
                        | "topObjectProperty"
                        | "owl:bottomObjectProperty"
                        | "bottomObjectProperty"
                ) {
                    unsupported.insert(format!("ObjectPropertyAssertion uses builtin role {role}"));
                    continue;
                }
                let covered = require_individual(
                    &by_individual,
                    &mut unsupported,
                    source,
                    "ObjectPropertyAssertion",
                ) & require_individual(
                    &by_individual,
                    &mut unsupported,
                    target,
                    "ObjectPropertyAssertion",
                );
                if covered {
                    role_assertions.insert(NominalRoleAssertionMeta {
                        role: role.clone(),
                        source: source.clone(),
                        target: target.clone(),
                    });
                }
            }
            Axiom::NegativeRoleAssertion(role, source, target) => {
                parsed_negative_role += 1;
                if matches!(
                    role.as_str(),
                    "owl:topObjectProperty"
                        | "topObjectProperty"
                        | "owl:bottomObjectProperty"
                        | "bottomObjectProperty"
                ) {
                    unsupported.insert(format!(
                        "NegativeObjectPropertyAssertion uses builtin role {role}"
                    ));
                    continue;
                }
                let covered = require_individual(
                    &by_individual,
                    &mut unsupported,
                    source,
                    "NegativeObjectPropertyAssertion",
                ) & require_individual(
                    &by_individual,
                    &mut unsupported,
                    target,
                    "NegativeObjectPropertyAssertion",
                );
                if covered {
                    negative_role_assertions.insert(NominalRoleAssertionMeta {
                        role: role.clone(),
                        source: source.clone(),
                        target: target.clone(),
                    });
                }
            }
            Axiom::DifferentIndividuals(left, right) => {
                parsed_different_pairs += 1;
                let covered = require_individual(
                    &by_individual,
                    &mut unsupported,
                    left,
                    "DifferentIndividuals",
                ) & require_individual(
                    &by_individual,
                    &mut unsupported,
                    right,
                    "DifferentIndividuals",
                );
                if covered {
                    let pair = if left <= right {
                        (left.clone(), right.clone())
                    } else {
                        (right.clone(), left.clone())
                    };
                    different.insert(pair);
                }
            }
            Axiom::SameIndividual(left, right) => {
                parsed_same_pairs += 1;
                let covered =
                    require_individual(&by_individual, &mut unsupported, left, "SameIndividual")
                        & require_individual(
                            &by_individual,
                            &mut unsupported,
                            right,
                            "SameIndividual",
                        );
                if covered {
                    let pair = if left <= right {
                        (left.clone(), right.clone())
                    } else {
                        (right.clone(), left.clone())
                    };
                    same.insert(pair);
                }
            }
            _ => {
                unsupported.insert("unsupported parsed ABox axiom".to_string());
            }
        }
    }
    for (individual, markers) in marker_queue {
        if !markers.is_empty() {
            unsupported.insert(format!(
                "{individual} has {} unmatched normalized ClassAssertion marker(s)",
                markers.len()
            ));
        }
    }

    let source_count = |kind: &str| source.axiom_types.get(kind).copied().unwrap_or(0);
    let source_object_role = source_count("ObjectPropertyAssertion");
    let source_negative_object_role = source_count("NegativeObjectPropertyAssertion");
    let source_data_role =
        source_count("DataPropertyAssertion") + source_count("NegativeDataPropertyAssertion");
    let source_same = source_count("SameIndividual");
    let source_different = source_count("DifferentIndividuals");
    let recognized_source_abox = source_count("ClassAssertion")
        + source_object_role
        + source_negative_object_role
        + source_data_role
        + source_same
        + source_different;

    if parsed_class != source.class_assertions {
        unsupported.insert(format!(
            "source/parsed ClassAssertion mismatch ({}/{parsed_class})",
            source.class_assertions
        ));
    }
    if parsed_role != source_object_role {
        unsupported.insert(format!(
            "source/parsed ObjectPropertyAssertion mismatch ({source_object_role}/{parsed_role})"
        ));
    }
    if parsed_negative_role != source_negative_object_role {
        unsupported.insert(format!(
            "source/parsed NegativeObjectPropertyAssertion mismatch ({source_negative_object_role}/{parsed_negative_role})"
        ));
    }
    if source_data_role != 0 {
        unsupported.insert(format!(
            "{source_data_role} data-property assertion axiom(s) are unsupported"
        ));
    }
    if (source_same == 0) != (parsed_same_pairs == 0) || parsed_same_pairs < source_same {
        unsupported.insert(format!(
            "source/parsed SameIndividual mismatch ({source_same}/{parsed_same_pairs})"
        ));
    }
    // The parser expands n-ary DifferentIndividuals into every semantic pair.
    // Every well-formed source axiom contributes at least one pair.
    if (source_different == 0) != (parsed_different_pairs == 0)
        || parsed_different_pairs < source_different
    {
        unsupported.insert(format!(
            "source/parsed DifferentIndividuals mismatch ({source_different}/{parsed_different_pairs})"
        ));
    }
    if recognized_source_abox != source.abox_axioms {
        unsupported.insert(format!(
            "{} source ABox axiom(s) have an unsupported constructor",
            source.abox_axioms.saturating_sub(recognized_source_abox)
        ));
    }
    if source.rule_axioms != 0 {
        unsupported.insert(format!(
            "{} DL-safe rule axiom(s) require a separate ABox contract",
            source.rule_axioms
        ));
    }
    for entry in by_individual.values() {
        if entry.proxies.is_empty() || entry.assertions.len() != entry.assertion_markers.len() {
            unsupported.insert(format!(
                "individual {} has incomplete proxy/assertion-marker coverage",
                entry.individual
            ));
        }
    }

    let unsupported: Vec<String> = unsupported.into_iter().collect();
    NominalAboxMeta {
        complete: unsupported.is_empty(),
        individuals: by_individual.into_values().collect(),
        same: same.into_iter().collect(),
        different: different.into_iter().collect(),
        role_assertions: role_assertions.into_iter().collect(),
        negative_role_assertions: negative_role_assertions.into_iter().collect(),
        unsupported,
    }
}

/// Borrowed concept names appearing in a list of JSON clauses. Declaration
/// seeding needs membership only; owning a second copy of every name made this
/// temporary set both allocation-heavy and needlessly ordered.
fn concept_names_in(clauses: &[crate::json_io::JClause]) -> HashSet<&str> {
    use crate::json_io::JAtom;
    let mut names = HashSet::new();
    for c in clauses {
        for atom in c.body.iter().chain(c.head.iter()) {
            if let JAtom::Concept { concept, .. } = atom {
                names.insert(concept.as_str());
            }
        }
    }
    names
}

fn seed_missing_declarations(clauses: &mut Vec<crate::json_io::JClause>, declared: &[String]) {
    let mut present = concept_names_in(clauses);
    let mut missing = Vec::new();
    for (index, name) in declared.iter().enumerate() {
        if present.insert(name.as_str()) {
            missing.push(index);
        }
    }
    // `present` borrows the clause vector. Release it before appending the
    // missing declaration tautologies, in source declaration order.
    drop(present);
    for index in missing {
        let name = &declared[index];
        let atom = Atom::Concept(name.clone(), Term::Var("x".to_string()));
        let self_cl: DLClause = clause([atom.clone()], [atom]);
        clauses.push(clause_to_json(&self_cl));
    }
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
    let requested = std::env::var("KM_ROUTE")
        .unwrap_or_else(|_| "manual".to_string())
        .parse::<crate::routing::Route>()
        .map_err(|error| parse::OutOfFragment(format!("configuration: {error}")))?;
    ofn_to_clauses_requested(text, requested)
}

/// Route-explicit frontend core. Production selects `requested` from KM_ROUTE;
/// tests use the wrapper below so they can exercise automatic routing without
/// relying on a pre-existing KM_ROUTE value.
fn ofn_to_clauses_requested(
    text: &str,
    requested: crate::routing::Route,
) -> Result<FrontendResult, parse::OutOfFragment> {
    let mut t = StageTimer::new();
    let mut reg = IriRegistry::new();
    // Pass 1: stream the document into SROIQ axioms. No token vector and no
    // document AST is ever materialised (both used to be O(document) with a
    // heap string per token, and the AST was additionally deep-cloned for the
    // rbox/declared scans — together the 20 GB peak on 500 MB ontologies).
    let mut profile_builder = profile::SourceProfileBuilder::new();
    let mut rule_certificate_scan = rule_certificate::RuleCertificateScan::default();
    let mut top_role_scan = top_role::TopRoleScan::default();
    // Side-channel observers retain only borrowed tokens, compact derived data,
    // and the RBox axiom subtrees that must be replayed after normalization.
    // None touches `reg`, so first-use internal-name assignment remains exactly
    // the primary parser's sequence.
    let mut raw_rbox = rbox::RawRbox::default();
    let mut declared_raw: Vec<&str> = Vec::new();
    let mut data_ranges = data_range::DataRanges::default();
    let mut data_abox = data_abox::DataAbox::default();
    let mut ontology = parse::parse_axioms_observed(&mut reg, text, |node| {
        profile_builder.observe(node);
        rule_certificate_scan.observe(node);
        top_role_scan.observe(node);
        raw_rbox.observe(node);
        data_ranges.observe(node);
        data_abox.observe(node);
        if let Some(name) = parse::declared_class_node(node) {
            declared_raw.push(name);
        }
    })?;
    // `R ⊑ owl:topObjectProperty` is a tautology. When it is the ontology's only
    // mention of the builtin, removing it keeps every entailment and every CB
    // derivation (nothing ever reads the write-only role) while letting the
    // procedures that fail closed on a universal role — the konclude_ht bridge
    // among them — see the terminology they can actually classify.
    // `KM_NO_TOP_ROLE_ELISION` restores the pre-elision clause and RBox output
    // for differential testing; it is not a routing switch.
    let elide_top_role =
        top_role_scan.eliminable() && std::env::var_os("KM_NO_TOP_ROLE_ELISION").is_none();
    if elide_top_role {
        let removed = top_role::elide_vacuous_inclusions(&mut ontology, &reg);
        if std::env::var_os("KM_DEBUG_TOP_ROLE").is_some() {
            eprintln!("KM_DEBUG_TOP_ROLE elided {removed} vacuous top-role inclusion(s)");
        }
    }
    let ontology = ontology;
    // Source features are now complete and their borrowed distinct-entity sets
    // can be freed before clausification. The learned router also makes its
    // pre-normalisation choice at this exact boundary.
    let mut profile = profile_builder.finish(text.len() as u64);
    // A certified rule/ABox clash makes the full ontology inconsistent before
    // worker selection. In that case unsupported source rules cannot restore
    // consistency, so it is safe to admit every independently certified
    // redundant rule and return the clash. Otherwise redundancy remains an
    // explicit opt-in until its downstream route meets the production budget.
    let rule_abox_inconsistent = rule_certificate_scan.certified_inconsistent();
    let available_rule_certificates = rule_certificate_scan.certified_unsupported_rules();
    let certified_unsupported_rules =
        if rule_abox_inconsistent || std::env::var_os("KM_RULE_REDUNDANCY_CERT").is_some() {
            available_rule_certificates
        } else {
            0
        };
    if std::env::var_os("KM_DEBUG_RULES").is_some() {
        eprintln!(
            "KM_DEBUG_RULES: {available_rule_certificates} redundancy certificate(s) available, {certified_unsupported_rules} enabled"
        );
    }
    profile.source.unsupported_rule_axioms = profile
        .source
        .unsupported_rule_axioms
        .saturating_sub(certified_unsupported_rules);
    let automatic = requested == crate::routing::Route::Auto;
    let mut route = if automatic {
        crate::routing::select(&profile)
    } else {
        requested
    };
    // Named bundles control clausification as well as the later worker. This
    // call occurs before normalisation and before any reasoner thread starts.
    route.apply_environment();
    // ELC computes bottom propagation as part of its own complete fixpoint.
    // Building the general SROIQ bottom certificate is therefore redundant on
    // an ELC-only route and can be quadratic on giant flat taxonomies with
    // many paths to owl:Nothing. Other routes retain the prepass unchanged.
    let mut bottom_prepass = if route_needs_bottom_prepass(route)
        && std::env::var_os("KM_NO_BOTTOM_PREPASS").is_none()
    {
        Some(bottom_prepass::BottomPrepass::from_ontology(&ontology))
    } else {
        None
    };
    // Bottom-role constraints are a subset of the retained RBox source nodes.
    // Derive them only for routes that use the prepass, matching the prior
    // conditional observer without reparsing the document.
    let mut bottom_role_constraints = bottom_prepass::RawRoleConstraints::default();
    if bottom_prepass.is_some() {
        for node in raw_rbox.source_nodes() {
            bottom_role_constraints.observe(node);
        }
    }
    t.lap("parse+axioms");
    let (tbox, abox, mut hooks) = normalise::normalise(&ontology);
    let mut nominal_abox = collect_nominal_abox(&ontology, &abox, &hooks, &profile.source);
    // Project the named-class ABox-consistency data before the AST is dropped
    // (cheap: `None` unless the ontology has named-class disjointness). The
    // clash check is finished after the RBox domain/range records are built.
    let abox_data = abox_consistency::collect(&ontology);
    let nominal_enumeration_inconsistent =
        abox_consistency::nominal_enumeration_inconsistent(&ontology);
    let (asserted_direct, asserted_roles) = abox_consistency::asserted_profile(&ontology);
    if std::env::var_os("KM_DEBUG_RULES").is_some() {
        eprintln!(
            "KM_DEBUG_RULES: parsed {} DL-safe SWRL rule(s)",
            ontology.rules().count()
        );
    }
    // SWRL DL-safe rule support (Stage 2): carry the parsed DL-safe rules to
    // cb_to_ht and (when any rule is present) keep the ground ABox in the clause
    // set so cb_to_ht can seed it as named-individual nominal nodes. Default ON,
    // opt out with KM_NO_HT_RULES. `collect_rules` returns EMPTY on a rule-free
    // ontology, so `ht_rules` stays false there and the output is byte-identical
    // to before. An active rule route rejects any rule shape it cannot encode;
    // silently dropping one would make a supposedly complete policy leaf
    // incomplete.
    let rules: Vec<crate::json_io::JRule> = if std::env::var_os("KM_NO_HT_RULES").is_none() {
        collect_rules(
            &ontology,
            profile.source.rule_axioms,
            certified_unsupported_rules,
        )?
    } else {
        Vec::new()
    };
    let ht_rules = !rules.is_empty();
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
    let cardinalities = std::mem::take(&mut hooks.cardinalities);
    let definers = std::mem::take(&mut hooks.definers);
    let source_axioms = std::mem::take(&mut hooks.source_axioms);
    // KM_HT_RULES: keep the ground ABox in the clause set so cb_to_ht can seed the
    // named individuals as nominal nodes (the rules + ABox consistency check runs
    // over that graph). Only when a rule is present (`ht_rules`), so a normal ABox
    // ontology is untouched.
    if ht_rules {
        tbox.extend(abox.iter().cloned());
    }
    drop(abox);
    drop(hooks);
    t.lap("augment");

    // Replay only retained RBox nodes after all primary axiom names have been
    // registered. This keeps every `reg.short` call in the same order as the
    // former full Pass 2, then declarations are resolved below as before.
    let mut rbox = raw_rbox.resolve(&mut reg);
    // The RBox is re-extracted from the source text, so it still carries the
    // rows of the inclusions elided above. They are what puts the builtin into
    // the TInput role table.
    if elide_top_role {
        top_role::elide_vacuous_rbox_rows(&mut rbox, &reg);
    }
    // asserted-ABox inconsistency: named-disjointness clash (abox_consistency)
    // or datatype range/functionality clash (data_abox); both sound prechecks.
    let abox_inconsistent = abox_data.map(|d| d.is_inconsistent(&rbox)).unwrap_or(false)
        || nominal_enumeration_inconsistent
        || data_abox.is_inconsistent()
        || rule_abox_inconsistent;
    if !abox_inconsistent && data_abox.positive_assertions_redundant() {
        let source_data_assertions = profile
            .source
            .axiom_types
            .get("DataPropertyAssertion")
            .copied()
            .unwrap_or(0);
        let diagnostic =
            format!("{source_data_assertions} data-property assertion axiom(s) are unsupported");
        nominal_abox
            .unsupported
            .retain(|reason| reason != &diagnostic);
        nominal_abox.complete = nominal_abox.unsupported.is_empty();
    }
    // Source routing initially keeps these ontologies on the exact nominal CB
    // calculus because data assertions are not known to be representable until
    // the parsed-AST certificate above has run. Once the complete typed payload
    // is proved, add the complete-answer-or-defer SHOIQ competitor while
    // retaining that same CB fallback.
    if automatic
        && route == crate::routing::Route::Nominals
        && nominal_abox.complete
        && crate::routing::nominal_ni_abox_candidate(&profile)
    {
        route = crate::routing::Route::NominalNiAbox;
        route.apply_environment();
        bottom_prepass = None;
    }
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
        tbox.extend(preprocess::domain_consumer_chain_clauses(
            &chain_info,
            &domain_range,
        ));
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
        preprocess::prune_inert_role_bridges(
            &mut tbox,
            &symmetric_roles,
            &role_inverses,
            &relevant,
        );
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
    // Resolve complex role constraints only after declarations have claimed
    // their established internal names. The prepass then materializes proven
    // bottom classes as ordinary constraints; no calculus rule changes.
    if let Some(prepass) = bottom_prepass {
        let role_constraints = bottom_role_constraints.resolve(&mut reg);
        let certified_bottom = prepass.certify(&role_constraints);
        tbox.extend(bottom_prepass::constraints(&certified_bottom));
        if std::env::var_os("KM_BOTTOM_PREPASS_STATS").is_some() {
            eprintln!(
                "BOTTOM-PREPASS seeds={} subclass={} exists={} contextual={} total={} forced={} markers={} incompatible={}",
                certified_bottom.seeds,
                certified_bottom.via_subclass,
                certified_bottom.via_existential,
                certified_bottom.contextual_roots,
                certified_bottom.classes.len(),
                certified_bottom.forced_subclasses.len(),
                certified_bottom.value_markers.len(),
                certified_bottom.incompatible_pairs.len(),
            );
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

    // KM_ABSORB_HOIST: common-disjunct hoisting (P3, Konclude
    // CCommonDisjunctConceptExtractionPreProcess). Adds the sound unit
    // consequence `⊤⊑X` for any X that subsumes every disjunct of a covering
    // disjunction `⊤⊑A₁∨…∨Aₙ`, letting subsumption prune disjunctive width
    // earlier. Pure clause ADDITION of an already-entailed fact ⇒ no re-cert,
    // and inert (adds nothing) on ontologies without covering disjunctions, so
    // default-off keeps output byte-identical to the prior binary.
    let tbox = if std::env::var_os("KM_ABSORB_HOIST").is_some() {
        let (t, n) = clauses::hoist_common_disjuncts(tbox);
        if std::env::var_os("KM_OFN_TIMING").is_some() {
            eprintln!("ofn [hoist] added {} common-disjunct unit facts", n);
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

    // ELC is the only learned leaf whose exact semantic domain is known only
    // after normalization. The source tree may propose it, but the worker is
    // authorized only when both the RBox relevance test and the cert-off ELC
    // normal-form screen pass. A rejection changes the route, not the result of
    // a speculative reasoner run: no race and no wasted classification worker.
    // ELC and plain CB use the same clausification-affecting settings (rules and
    // absorption off), so applying the final CB bundle here preserves exactly
    // the clauses just constructed while configuring the parent orchestrator's
    // one selected worker.
    if automatic
        && route == crate::routing::Route::Elc
        && (!el_rbox_safe || !crate::elcomplete::is_pure_el_shape(&jclauses))
    {
        route = crate::routing::Route::CbPlain16;
        route.apply_environment();
    }

    // Seed every declared class absent from the clause set with a tautological
    // self-clause A(x) → A(x) (port of the declared-classes loop).
    seed_missing_declarations(&mut jclauses, &declared);

    // iri_map / named: every internal name registered to a real IRI, EXCEPT
    // anonymous blank nodes (`_:genidN` — OWL structure nodes for complex
    // class expressions / restrictions). On ABox-heavy ontologies these
    // dominate the meta (ore_ont_10073: 457675 of 473278 entries, 21 MB → the
    // ofn serialisation + the orchestrator's meta parse both scale with it).
    // A blank node is never a queryable NAMED class and a `_:genidN` string in
    // the class-hierarchy output is meaningless, so excluding it from both the
    // query/output `named` set and the output `iri_map` is output-neutral (the
    // blank-node CONCEPT stays in the clause set — only its query/output
    // registration is dropped). Gated by KM_KEEP_BLANK_NAMES for A/B.
    let drop_blank = std::env::var_os("KM_KEEP_BLANK_NAMES").is_none();
    let mut iri_entries: Vec<(String, String)> = reg
        .owned_entries()
        .filter(|(_, iri)| !drop_blank || !iri.starts_with("_:"))
        .map(|(internal, iri)| (internal.to_string(), iri.to_string()))
        .collect();
    iri_entries.sort_unstable_by(|left, right| left.0.cmp(&right.0));
    let named = iri_entries
        .iter()
        .map(|(internal, _)| internal.clone())
        .collect();
    // The iterator is already in key order. `BTreeMap` can bulk-extend its
    // right edge instead of performing a second independent ordering pass.
    let iri_map = iri_entries.into_iter().collect();
    t.lap("declared_seed+iri_map");

    // The deployable tree uses source/expressivity features because it must
    // choose before normalisation. A second full scan of multi-million-clause
    // giants would add classification time without influencing that choice.
    // `km profile` requests this detailed channel explicitly; ordinary
    // classification carries zeroed clause statistics in its meta.
    if std::env::var_os("KM_PROFILE_CLAUSES").is_some() {
        profile.clauses = profile::clause_statistics(&jclauses);
    }

    let rbox = rbox.iter().map(rbox::to_row).collect();
    Ok(FrontendResult {
        clauses: jclauses,
        rbox,
        iri_map,
        named,
        declared,
        el_rbox_safe,
        abox_inconsistent,
        asserted_classes: asserted_classes.into_iter().collect(),
        nominal_abox,
        cardinalities,
        definers,
        source_axioms,
        rules,
        profile,
        route: route.as_str().to_string(),
    })
}

fn route_needs_bottom_prepass(route: crate::routing::Route) -> bool {
    !matches!(
        route,
        crate::routing::Route::Elc | crate::routing::Route::ElcCert
    )
}

#[cfg(test)]
pub(crate) fn with_ofn_to_clauses_requested_route<T>(
    text: &str,
    requested: crate::routing::Route,
    consume: impl FnOnce(FrontendResult) -> T,
) -> Result<T, parse::OutOfFragment> {
    let _guard = crate::routing::EnvironmentGuard::capture();
    ofn_to_clauses_requested(text, requested).map(consume)
}

#[cfg(test)]
mod bottom_prepass_route_tests {
    use super::{route_needs_bottom_prepass, seed_missing_declarations};
    use crate::frontend::iri::IriRegistry;
    use crate::frontend::{bottom_prepass, clauses, data_abox, data_range, parse, rbox};
    use crate::json_io::JAtom;
    use crate::routing::Route;

    #[derive(Debug, PartialEq, Eq)]
    struct SideBytes {
        rbox: Vec<u8>,
        declared: Vec<u8>,
        empty_ranges: Vec<u8>,
        bottom: bottom_prepass::BottomPrepassResult,
        data_inconsistent: bool,
        data_redundant: bool,
        registry: Vec<u8>,
    }

    fn finish_side_scan<'a>(
        mut registry: IriRegistry,
        rbox_records: Vec<rbox::RboxRecord>,
        declared_raw: Vec<&'a str>,
        data_ranges: data_range::DataRanges,
        data_abox: data_abox::DataAbox<'a>,
        raw_roles: bottom_prepass::RawRoleConstraints,
        bottom: bottom_prepass::BottomPrepass,
    ) -> SideBytes {
        let declared: Vec<_> = declared_raw
            .into_iter()
            .map(|name| registry.short(name))
            .filter(|name| name != "owl:Thing" && name != "owl:Nothing")
            .collect();
        let bottom = bottom.certify(&raw_roles.resolve(&mut registry));
        let empty_ranges: Vec<_> = data_ranges
            .empty_range_constraints(&mut registry)
            .iter()
            .map(clauses::clause_to_json)
            .collect();
        let mut registry_entries: Vec<_> = registry
            .owned_entries()
            .map(|(name, iri)| (name.to_string(), iri.to_string()))
            .collect();
        registry_entries.sort_unstable();
        SideBytes {
            rbox: serde_json::to_vec(&rbox_records.iter().map(rbox::to_row).collect::<Vec<_>>())
                .unwrap(),
            declared: serde_json::to_vec(&declared).unwrap(),
            empty_ranges: serde_json::to_vec(&empty_ranges).unwrap(),
            bottom,
            data_inconsistent: data_abox.is_inconsistent(),
            data_redundant: data_abox.positive_assertions_redundant(),
            registry: serde_json::to_vec(&registry_entries).unwrap(),
        }
    }

    #[test]
    fn el_completion_does_not_build_the_general_bottom_certificate() {
        assert!(!route_needs_bottom_prepass(Route::Elc));
        assert!(!route_needs_bottom_prepass(Route::ElcCert));
        assert!(route_needs_bottom_prepass(Route::ProductionAll));
        assert!(route_needs_bottom_prepass(Route::CbPlain16));
    }

    #[test]
    fn absent_declarations_are_seeded_once_in_source_order() {
        let mut clauses = Vec::new();
        let declared = vec!["Z".to_string(), "A".to_string(), "Z".to_string()];
        seed_missing_declarations(&mut clauses, &declared);
        let seeded: Vec<&str> = clauses
            .iter()
            .filter_map(|clause| match (&clause.body[..], &clause.head[..]) {
                (
                    [JAtom::Concept { concept: body, .. }],
                    [JAtom::Concept { concept: head, .. }],
                ) if body == head => Some(body.as_str()),
                _ => None,
            })
            .collect();
        assert_eq!(seeded, vec!["Z", "A"]);
    }

    #[test]
    fn retained_side_observers_match_v025_second_pass_bytes() {
        let text = "Ontology(\
            Declaration(Class(<http://decl.example#A>)) \
            Declaration(Class(<http://other.example#A>)) \
            SubClassOf(<http://decl.example#A> owl:Nothing) \
            ObjectPropertyDomain(<http://role.example#r> <http://decl.example#A>) \
            ObjectPropertyRange(ObjectInverseOf(<http://role.example#s>) ObjectUnionOf(<http://decl.example#A> <http://other.example#A>)) \
            DataPropertyRange(<http://data.example#p> DataOneOf(\"a\"^^xsd:string)) \
            DataPropertyRange(<http://data.example#p> DataOneOf(\"b\"^^xsd:string)) \
            DataPropertyAssertion(<http://data.example#p> <http://individual.example#i> \"a\"^^xsd:string))";

        let mut retained_registry = IriRegistry::new();
        let mut raw_rbox = rbox::RawRbox::default();
        let mut retained_declared = Vec::new();
        let mut retained_ranges = data_range::DataRanges::default();
        let mut retained_abox = data_abox::DataAbox::default();
        let retained_ontology =
            parse::parse_axioms_observed(&mut retained_registry, text, |node| {
                raw_rbox.observe(node);
                retained_ranges.observe(node);
                retained_abox.observe(node);
                if let Some(name) = parse::declared_class_node(node) {
                    retained_declared.push(name);
                }
            })
            .unwrap();
        let retained_bottom = bottom_prepass::BottomPrepass::from_ontology(&retained_ontology);
        let mut retained_roles = bottom_prepass::RawRoleConstraints::default();
        for node in raw_rbox.source_nodes() {
            retained_roles.observe(node);
        }
        let retained_records = raw_rbox.resolve(&mut retained_registry);
        let retained = finish_side_scan(
            retained_registry,
            retained_records,
            retained_declared,
            retained_ranges,
            retained_abox,
            retained_roles,
            retained_bottom,
        );

        let mut legacy_registry = IriRegistry::new();
        let legacy_ontology = parse::parse_axioms(&mut legacy_registry, text).unwrap();
        let legacy_bottom = bottom_prepass::BottomPrepass::from_ontology(&legacy_ontology);
        let mut legacy_records = Vec::new();
        let mut legacy_declared = Vec::new();
        let mut legacy_ranges = data_range::DataRanges::default();
        let mut legacy_abox = data_abox::DataAbox::default();
        let mut legacy_roles = bottom_prepass::RawRoleConstraints::default();
        parse::for_each_ontology_child(text, |node| {
            rbox::rbox_node(&mut legacy_registry, node, &mut legacy_records);
            legacy_ranges.observe(node);
            legacy_abox.observe(node);
            legacy_roles.observe(node);
            if let Some(name) = parse::declared_class_node(node) {
                legacy_declared.push(name);
            }
            Ok(())
        })
        .unwrap();
        let legacy = finish_side_scan(
            legacy_registry,
            legacy_records,
            legacy_declared,
            legacy_ranges,
            legacy_abox,
            legacy_roles,
            legacy_bottom,
        );

        assert_eq!(retained, legacy);
    }
}

/// Convert the ontology's parsed `DLSafeRule` axioms into the JSON rule channel
/// (`JRule`). The rule fragment has three tiers:
///
///   * FIRED — every atom is a `ClassAtom` over a *named* class, an
///     `ObjectPropertyAtom`, or a `SameIndividualAtom`. These reach the fast Ht
///     and fire (`cb_to_ht::build_rule_clause`); a body `SameAs` unifies its two
///     terms, a head `SameAs` derives an equality.
///   * DEFERRED — the rule additionally carries a `DifferentIndividualsAtom`. It
///     is carried through here but dropped at firing time (the fast Ht tracks no
///     node distinctness). Dropping a rule from the one-sided consistency
///     precheck is sound: a lost constraint can lose an inconsistency, never
///     invent one. This is why a Diff-bearing rule does NOT decline the route
///     (that would forfeit the fired rules that DO detect 2669/15516's clash).
///   * DECLINED — the rule has an atom the parser cannot represent at all
///     (`DataPropertyAtom` / `BuiltInAtom` / `DataRangeAtom`, i.e. a concrete
///     domain), or a `ClassAtom` over a complex class expression. The parser
///     omits that AST rule, so `parsed < source` here and the whole rule-aware
///     route is REJECTED rather than silently dropped: a datatype/built-in
///     obligation is not an approximable constraint, so KM declines (the honest
///     ORE 10860 decline: 4 of its 17 rules use SWRL built-ins).
fn collect_rules(
    ontology: &syntax::Ontology,
    source_rule_count: u64,
    certified_unsupported_rules: u64,
) -> Result<Vec<crate::json_io::JRule>, parse::OutOfFragment> {
    use crate::json_io::{JRule, JRuleAtom, JRuleTerm};
    use syntax::{Axiom, Concept, RuleAtom, RuleTerm};
    let term = |t: &RuleTerm| -> JRuleTerm {
        match t {
            RuleTerm::Var(n) => JRuleTerm::Var { name: n.clone() },
            RuleTerm::Ind(n) => JRuleTerm::Ind { name: n.clone() },
        }
    };
    // a rule atom is representable only if every ClassAtom is over a *named* class.
    let conv_atom = |a: &RuleAtom| -> Option<JRuleAtom> {
        Some(match a {
            RuleAtom::Class(Concept::Name(c), t) => JRuleAtom::Class {
                concept: c.clone(),
                term: term(t),
            },
            RuleAtom::Class(_, _) => return None, // complex class expression: drop the rule
            RuleAtom::Role(r, s, t) => JRuleAtom::Role {
                role: r.clone(),
                source: term(s),
                target: term(t),
            },
            RuleAtom::Same(l, r) => JRuleAtom::Same {
                left: term(l),
                right: term(r),
            },
            RuleAtom::Diff(l, r) => JRuleAtom::Diff {
                left: term(l),
                right: term(r),
            },
        })
    };
    let parsed_rule_count = ontology.rules().count() as u64;
    if parsed_rule_count + certified_unsupported_rules != source_rule_count {
        return Err(parse::OutOfFragment(format!(
            "DL-safe rules: parsed {parsed_rule_count} and certified {certified_unsupported_rules} of {source_rule_count}; an atom or head shape is unsupported"
        )));
    }
    let mut out = Vec::new();
    for ax in ontology.rules() {
        if let Axiom::Rule(body, head) = ax {
            let jb: Option<Vec<_>> = body.iter().map(&conv_atom).collect();
            let jh: Option<Vec<_>> = head.iter().map(&conv_atom).collect();
            let (Some(b), Some(h)) = (jb, jh) else {
                return Err(parse::OutOfFragment(
                    "DL-safe rule contains a complex class atom".to_string(),
                ));
            };
            out.push(JRule { body: b, head: h });
        }
    }
    Ok(out)
}

#[cfg(test)]
mod rule_contract_tests {
    use super::*;

    fn ontology(text: &str) -> syntax::Ontology {
        let mut registry = IriRegistry::new();
        parse::parse_axioms(&mut registry, text).expect("rule test ontology")
    }

    #[test]
    fn named_dl_safe_rule_is_fully_representable() {
        let parsed = ontology(
            "Ontology(DLSafeRule(Body(ClassAtom(<A> Variable(<x>))) Head(ClassAtom(<B> Variable(<x>)))))",
        );
        assert_eq!(
            collect_rules(&parsed, 1, 0).expect("supported rule").len(),
            1
        );
    }

    #[test]
    fn rule_contract_rejects_dropped_and_complex_atoms() {
        let dropped = ontology(
            "Ontology(DLSafeRule(Body(BuiltInAtom(<p> Variable(<x>))) Head(ClassAtom(<B> Variable(<x>)))))",
        );
        assert!(collect_rules(&dropped, 1, 0).is_err());

        let complex = ontology(
            "Ontology(DLSafeRule(Body(ClassAtom(ObjectIntersectionOf(<A> <B>) Variable(<x>))) Head(ClassAtom(<C> Variable(<x>)))))",
        );
        assert!(collect_rules(&complex, 1, 0).is_err());
    }

    #[test]
    fn same_individual_rule_is_representable() {
        // SameIndividual is in the FIRED tier: the contract accepts it (it fires
        // downstream via variable identification / a derived equality).
        let parsed = ontology(
            "Ontology(DLSafeRule(Body(ClassAtom(<A> Variable(<x>)) SameIndividualAtom(Variable(<x>) Variable(<y>))) Head(ClassAtom(<B> Variable(<x>)))))",
        );
        let rules = collect_rules(&parsed, 1, 0).expect("SameAs rule accepted");
        assert_eq!(rules.len(), 1);
    }

    #[test]
    fn different_individuals_rule_does_not_decline_the_route() {
        // DEFERRED tier: a Diff-bearing rule is carried through the contract (it
        // must NOT decline the route — that would forfeit the fired rules that
        // detect the 2669/15516 clash). It is dropped at firing time instead.
        let parsed = ontology(
            "Ontology(DLSafeRule(Body(ObjectPropertyAtom(<r> Variable(<x>) Variable(<y>)) DifferentIndividualsAtom(Variable(<x>) Variable(<y>))) Head(ClassAtom(<B> Variable(<x>)))))",
        );
        let rules = collect_rules(&parsed, 1, 0).expect("Diff rule carried, route not declined");
        assert_eq!(
            rules.len(),
            1,
            "the rule is represented (Diff dropped only at firing)"
        );

        // A mixed corpus (one fired + one deferred) is still accepted wholesale.
        let mixed = ontology(
            "Ontology(\
DLSafeRule(Body(ClassAtom(<A> Variable(<x>))) Head(ClassAtom(<B> Variable(<x>)))) \
DLSafeRule(Body(ObjectPropertyAtom(<r> Variable(<x>) Variable(<y>)) DifferentIndividualsAtom(Variable(<x>) Variable(<y>))) Head(ClassAtom(<C> Variable(<x>)))))",
        );
        assert_eq!(
            collect_rules(&mixed, 2, 0).expect("mixed accepted").len(),
            2
        );
    }

    #[test]
    fn builtin_bearing_corpus_declines_even_with_representable_rules() {
        // Negative contract: one built-in rule beside representable rules still
        // declines the whole route (the honest ORE 10860 shape). The parser drops
        // the built-in rule, so parsed (1) < source (2) and collect_rules errs.
        let parsed = ontology(
            "Ontology(\
DLSafeRule(Body(ClassAtom(<A> Variable(<x>))) Head(ClassAtom(<B> Variable(<x>)))) \
DLSafeRule(Body(BuiltInAtom(<gt> Variable(<x>) \"5\")) Head(ClassAtom(<C> Variable(<x>)))))",
        );
        assert!(
            collect_rules(&parsed, 2, 0).is_err(),
            "a concrete-domain built-in rule declines the route wholesale"
        );
    }
}

#[cfg(test)]
mod nominal_abox_contract_tests {
    use super::*;

    const PREFIX: &str = "Prefix(:=<http://example.org/>)\nOntology(";

    #[test]
    fn nary_different_individuals_is_certified_as_exact_pairs() {
        let result = ofn_to_clauses(&format!(
            "{PREFIX}\
             Declaration(Class(:A))\
             Declaration(Class(:OnlyA)) Declaration(Class(:OnlyB)) Declaration(Class(:OnlyC))\
             Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b)) Declaration(NamedIndividual(:c))\
             EquivalentClasses(:OnlyA ObjectOneOf(:a))\
             EquivalentClasses(:OnlyB ObjectOneOf(:b))\
             EquivalentClasses(:OnlyC ObjectOneOf(:c))\
             ClassAssertion(:A :a)\
             DifferentIndividuals(:a :b :c))"
        ))
        .expect("nominal ontology is parsed");
        let meta = result.nominal_abox;
        assert!(meta.complete, "coverage reasons: {:?}", meta.unsupported);
        assert_eq!(meta.individuals.len(), 3);
        assert_eq!(
            meta.different.len(),
            3,
            "three-way Different expands pairwise"
        );
        assert_eq!(
            meta.individuals
                .iter()
                .map(|entry| entry.assertions.len())
                .sum::<usize>(),
            1
        );
        assert!(meta
            .individuals
            .iter()
            .all(|entry| !entry.proxies.is_empty()));
    }

    #[test]
    fn object_abox_and_assertion_only_individuals_are_certified() {
        let result = ofn_to_clauses(&format!(
            "{PREFIX}\
             Declaration(ObjectProperty(:r))\
             Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))\
             ObjectPropertyAssertion(:r :a :b))"
        ))
        .expect("object ABox is parsed");
        assert!(
            result.nominal_abox.complete,
            "coverage reasons: {:?}",
            result.nominal_abox.unsupported
        );
        assert_eq!(result.nominal_abox.role_assertions.len(), 1);

        let result = ofn_to_clauses(&format!(
            "{PREFIX}\
             Declaration(Class(:A)) Declaration(NamedIndividual(:a))\
             ClassAssertion(:A :a))"
        ))
        .expect("plain class assertion ontology is parsed");
        assert!(
            result.nominal_abox.complete,
            "coverage reasons: {:?}",
            result.nominal_abox.unsupported
        );
        assert_eq!(result.nominal_abox.individuals.len(), 1);
        assert_eq!(result.nominal_abox.individuals[0].assertions.len(), 1);
        assert_eq!(
            result.nominal_abox.individuals[0].assertion_markers.len(),
            1
        );
        assert!(!result.nominal_abox.individuals[0].proxies.is_empty());
    }

    #[test]
    fn identity_is_retained_while_data_fails_and_negative_object_roles_are_retained() {
        let result = ofn_to_clauses(&format!(
            "{PREFIX}\
             Declaration(Class(:OnlyA)) Declaration(Class(:OnlyB))\
             Declaration(ObjectProperty(:r)) Declaration(DataProperty(:p))\
             Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))\
             EquivalentClasses(:OnlyA ObjectOneOf(:a))\
             EquivalentClasses(:OnlyB ObjectOneOf(:b))\
             SameIndividual(:a :b)\
             NegativeObjectPropertyAssertion(:r :a :b)\
             NegativeDataPropertyAssertion(:p :a \"x\"))"
        ))
        .expect("unsupported ABox constructs are still profiled");
        assert!(!result.nominal_abox.complete);
        assert_eq!(result.nominal_abox.same.len(), 1);
        assert!(result
            .nominal_abox
            .unsupported
            .iter()
            .any(|reason| reason.contains("data-property assertion")));
        assert_eq!(result.nominal_abox.negative_role_assertions.len(), 1);
    }

    #[test]
    fn typed_abox_preserves_class_roles_negatives_and_different() {
        let result = ofn_to_clauses(&format!(
            "{PREFIX}\
             Declaration(Class(:A)) Declaration(Class(:B))\
             Declaration(ObjectProperty(:r))\
             Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))\
             ClassAssertion(ObjectIntersectionOf(:A :B) :a)\
             ObjectPropertyAssertion(:r :a :b)\
             NegativeObjectPropertyAssertion(:r :b :a)\
             DifferentIndividuals(:a :b))"
        ))
        .expect("typed object ABox parses");
        let meta = result.nominal_abox;
        assert!(meta.complete, "coverage reasons: {:?}", meta.unsupported);
        assert_eq!(meta.individuals.len(), 2);
        assert_eq!(meta.different.len(), 1);
        assert_eq!(meta.role_assertions.len(), 1);
        assert_eq!(meta.negative_role_assertions.len(), 1);
        let a = meta
            .individuals
            .iter()
            .find(|entry| entry.individual == "a")
            .unwrap();
        assert_eq!(a.assertions.len(), 1);
        assert_eq!(a.assertion_markers.len(), 1);
        assert!(!a.proxies.is_empty());
    }

    #[test]
    fn assertion_only_proxy_uses_normalizer_mapping_without_default_clause_injection() {
        let mut registry = IriRegistry::new();
        let ontology = parse::parse_axioms(
            &mut registry,
            &format!(
                "{PREFIX}\
                 Declaration(Class(:A)) Declaration(Class(:__nom__a))\
                 Declaration(NamedIndividual(:a)) SubClassOf(:__nom__a :A)\
                 ClassAssertion(:A :a))"
            ),
        )
        .expect("collision probe parses");
        let (_tbox, _abox, hooks) = normalise::normalise(&ontology);
        assert!(
            hooks.nominal_to_individual.is_empty(),
            "assertion-only individuals must not change ordinary nominal preprocessing"
        );
        assert_eq!(
            hooks.abox_nominal_to_individual.get("__nom__a"),
            Some(&"a".to_string())
        );
        let generated = "__nom__a";
        let source_class = registry
            .owned_names()
            .into_iter()
            .find(|name| registry.full_iri(name) == ":__nom__a")
            .expect("source generated-looking class retained");
        assert_ne!(generated, source_class);
        assert!(source_class.starts_with("km_src_"));
    }

    #[test]
    fn identity_and_redundant_positive_data_are_complete_while_unsupported_abox_fails_closed() {
        let identity = ofn_to_clauses(&format!(
            "{PREFIX} Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b)) SameIndividual(:a :b))"
        ))
        .expect("identity ABox parses")
        .nominal_abox;
        assert!(identity.complete);
        assert_eq!(identity.same, vec![("a".into(), "b".into())]);

        let redundant_positive_data = ofn_to_clauses(&format!(
            "{PREFIX} Declaration(DataProperty(:p)) Declaration(NamedIndividual(:a)) DataPropertyAssertion(:p :a \"x\"))"
        ))
        .expect("redundant positive data ABox parses")
        .nominal_abox;
        assert!(
            redundant_positive_data.complete,
            "the data-ABox certificate proves this unconstrained positive assertion redundant: {:?}",
            redundant_positive_data.unsupported
        );

        for (source, expected) in [
            (
                format!(
                    "{PREFIX} Declaration(DataProperty(:p)) Declaration(NamedIndividual(:a)) NegativeDataPropertyAssertion(:p :a \"x\"))"
                ),
                "data-property assertion",
            ),
            (
                format!(
                    "{PREFIX} Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b)) ObjectPropertyAssertion(owl:bottomObjectProperty :a :b))"
                ),
                "builtin role",
            ),
        ] {
            let meta = ofn_to_clauses(&source)
                .expect("unsupported ABox still parses for fail-closed metadata")
                .nominal_abox;
            assert!(!meta.complete, "unsupported ABox was certified: {source}");
            assert!(
                meta.unsupported.iter().any(|reason| reason.contains(expected)),
                "{expected}: {:?}",
                meta.unsupported
            );
        }
    }
}
