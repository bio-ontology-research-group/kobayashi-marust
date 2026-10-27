//! Realization: the entailed named types of every named individual and the
//! entailed equalities between named individuals (`km classify --realize`).
//!
//! # Semantics
//!
//! For a consistent ontology `O`, a named individual `a` and a named class `C`
//! other than `owl:Thing`:
//!
//! * `TYPE a C` is reported iff `O ⊨ C(a)` (mode [`TypeMode::All`]), or iff
//!   additionally no reported type `D` of `a` satisfies `O ⊨ D ⊑ C` and
//!   `O ⊭ C ⊑ D` (mode [`TypeMode::Direct`]);
//! * `SAME a b` is reported, once per unordered pair with `a < b`, iff
//!   `a ≠ b` and `O ⊨ a = b`.
//!
//! An individual with no `TYPE` row has `owl:Thing` as its only type. For an
//! inconsistent ontology the classification reports `CONSISTENT 0` and no
//! `TYPE` or `SAME` rows are written (every assertion is entailed).
//!
//! # Mechanism
//!
//! None of KM's reasoning routes currently publishes a completeness guarantee
//! for ground facts `C(a)`: the EL++ completion rejects individual terms, the
//! TBox-only routes do not place the ABox in the saturated clause set, and the
//! consequence-based and hypertableau routes are complete for query-class
//! subsumption, not for unit ground facts under their literal orderings.
//! Reading types from a saturated state would therefore need a new
//! completeness argument (and Lean re-certification for the CB calculus).
//!
//! Realization therefore uses the exact reduction to classification. For each
//! named individual `a` of the source signature, a fresh class `P_a` with
//! `P_a ≡ {a}` is added. This is a conservative extension: it entails no new
//! subsumption between source names. Then, for a consistent `O`,
//! `O ⊨ C(a)` iff `O' ⊨ P_a ⊑ C`, and `O ⊨ a = b` iff `O' ⊨ P_a ⊑ P_b`.
//! The extended ontology is classified once by the ordinary production
//! pipeline, so every route that classifies it exactly also realizes `O`
//! exactly. Rows that mention a probe class are then removed from the
//! taxonomy, which leaves the classification of `O` itself.

use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::io::Write;
use std::path::Path;

use crate::frontend::sexpr::{self, Node};

use super::{tmpfile, Classification, Config, OrchestrateError, TrustedRewrite};

const OWL_THING: &str = "http://www.w3.org/2002/07/owl#Thing";

/// Diagnostic override: realize under a manually forced route.
pub const ANY_ROUTE_ENV: &str = "KM_REALIZE_ANY_ROUTE";

/// Which entailed types `TYPE` rows report.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TypeMode {
    /// Every entailed named type except `owl:Thing`.
    All,
    /// The most specific entailed named types (all members of each minimal
    /// equivalence class), except `owl:Thing`.
    Direct,
}

/// The classification of an ontology together with its realization.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Realization {
    /// The classification of the source ontology, as `km classify` reports it.
    pub classification: Classification,
    /// `[individual, class]` rows, sorted.
    pub types: Vec<[String; 2]>,
    /// `[a, b]` rows with `a < b`, sorted.
    pub same: Vec<[String; 2]>,
}

/// The source spelling of every named individual that occurs in an OFN
/// document, in first-occurrence order and without duplicates.
///
/// Individuals are the arguments in individual position of declarations,
/// assertions, `SameIndividual`/`DifferentIndividuals`, `ObjectOneOf`,
/// `ObjectHasValue` and DL-safe rule atoms. Anonymous individuals (`_:x`) are
/// not named individuals and are skipped. Annotation values are IRIs, not
/// individuals.
pub fn source_individuals(text: &str) -> Result<Vec<String>, OrchestrateError> {
    let mut seen: HashSet<&str> = HashSet::new();
    let mut ordered: Vec<String> = Vec::new();
    crate::frontend::parse::for_each_ontology_child(text, |node| {
        let mut found = Vec::new();
        individuals_in(node, &mut found);
        for token in found {
            if seen.insert(token) {
                ordered.push(token.to_string());
            }
        }
        Ok(())
    })
    .map_err(|error| OrchestrateError::OutOfFragment(error.0))?;
    Ok(ordered)
}

fn push_individual<'a>(node: Option<&&Node<'a>>, out: &mut Vec<&'a str>) {
    if let Some(Node::Atom(token)) = node.copied() {
        if !token.starts_with('"') && !token.starts_with("_:") {
            out.push(token);
        }
    }
}

fn individuals_in<'a>(node: &Node<'a>, out: &mut Vec<&'a str>) {
    let Node::List(head, args) = node else { return };
    let plain: Vec<&Node<'a>> = args
        .iter()
        .filter(|arg| arg.head() != Some("Annotation"))
        .collect();
    match *head {
        "Annotation" | "AnnotationAssertion" | "SubAnnotationPropertyOf"
        | "AnnotationPropertyDomain" | "AnnotationPropertyRange" | "Prefix" | "Import" => {}
        "Declaration" => {
            if let Some(Node::List("NamedIndividual", inner)) = plain.first().copied() {
                if let Some(Node::Atom(token)) = inner.first() {
                    if !token.starts_with("_:") {
                        out.push(token);
                    }
                }
            }
        }
        "ClassAssertion" => {
            if let Some(class) = plain.first() {
                individuals_in(class, out);
            }
            push_individual(plain.get(1), out);
        }
        "ObjectPropertyAssertion" | "NegativeObjectPropertyAssertion" => {
            push_individual(plain.get(1), out);
            push_individual(plain.get(2), out);
        }
        "DataPropertyAssertion" | "NegativeDataPropertyAssertion" => {
            push_individual(plain.get(1), out);
        }
        "SameIndividual" | "DifferentIndividuals" | "ObjectOneOf" => {
            for arg in &plain {
                push_individual(Some(arg), out);
            }
        }
        "ObjectHasValue" => push_individual(plain.get(1), out),
        // DL-safe rule atoms: a non-variable argument is a named individual.
        "ClassAtom" => {
            if let Some(class) = plain.first() {
                individuals_in(class, out);
            }
            push_individual(plain.get(1), out);
        }
        "ObjectPropertyAtom" => {
            push_individual(plain.get(1), out);
            push_individual(plain.get(2), out);
        }
        "DataPropertyAtom" => push_individual(plain.get(1), out),
        "SameIndividualAtom" | "DifferentIndividualsAtom" => {
            push_individual(plain.first(), out);
            push_individual(plain.get(1), out);
        }
        "BuiltInAtom" | "DataRangeAtom" => {}
        _ => {
            for arg in &plain {
                individuals_in(arg, out);
            }
        }
    }
}

/// The public name of a source token, as the classification output spells
/// class names: the IRI without its angle brackets, otherwise the token.
fn public_name(token: &str) -> String {
    token
        .strip_prefix('<')
        .and_then(|inner| inner.strip_suffix('>'))
        .unwrap_or(token)
        .to_string()
}

/// Byte offset of the `)` that closes the document's `Ontology(` node.
fn ontology_close_offset(text: &str) -> Option<usize> {
    let mut depth = 0usize;
    let mut previous: Option<&str> = None;
    let mut inside = false;
    for token in sexpr::tokens(text) {
        match token {
            "(" => {
                if depth == 0 && previous == Some("Ontology") {
                    inside = true;
                }
                depth += 1;
            }
            ")" => {
                depth = depth.checked_sub(1)?;
                if depth == 0 && inside {
                    return Some(token.as_ptr() as usize - text.as_ptr() as usize);
                }
            }
            _ => {}
        }
        previous = Some(token);
    }
    None
}

/// A probe-class namespace whose IRIs do not occur in `text`.
fn fresh_namespace(text: &str) -> String {
    let mut namespace = "http://km.invalid/realize#".to_string();
    let mut nonce = 0u64;
    while text.contains(namespace.trim_end_matches('#')) {
        nonce += 1;
        namespace = format!("http://km.invalid/realize{nonce}#");
    }
    namespace
}

/// The source extended with one probe class `P ≡ {a}` per named individual,
/// and the probe IRI (as the output spells it) for each individual's public
/// name.
fn probe_source(text: &str, individuals: &[String]) -> Result<(String, Vec<(String, String)>), OrchestrateError> {
    let close = ontology_close_offset(text).ok_or_else(|| {
        OrchestrateError::InvalidOntology("realization: no complete Ontology(...) node".into())
    })?;
    let namespace = fresh_namespace(text);
    let mut extension = String::with_capacity(individuals.len() * 128 + 2);
    let mut probes = Vec::with_capacity(individuals.len());
    extension.push('\n');
    for (index, token) in individuals.iter().enumerate() {
        let probe = format!("{namespace}individual{index}");
        extension.push_str(&format!(
            "Declaration(Class(<{probe}>))\nEquivalentClasses(<{probe}> ObjectOneOf({token}))\n"
        ));
        probes.push((probe, public_name(token)));
    }
    let mut extended = String::with_capacity(text.len() + extension.len());
    extended.push_str(&text[..close]);
    extended.push_str(&extension);
    extended.push_str(&text[close..]);
    Ok((extended, probes))
}

/// Split the classification of the probe-extended ontology into the source
/// classification and its realization.
fn split(
    mut extended: Classification,
    probes: &[(String, String)],
    mode: TypeMode,
) -> Result<Realization, OrchestrateError> {
    let individual_of: BTreeMap<&str, &str> = probes
        .iter()
        .map(|(probe, individual)| (probe.as_str(), individual.as_str()))
        .collect();
    let is_probe = |name: &str| individual_of.contains_key(name);

    let mut types: BTreeMap<&str, BTreeSet<String>> = BTreeMap::new();
    let mut same: BTreeSet<[String; 2]> = BTreeSet::new();
    let mut source_rows = Vec::with_capacity(extended.subsumptions.len());
    for [sub, sup] in std::mem::take(&mut extended.subsumptions) {
        match (individual_of.get(sub.as_str()), individual_of.get(sup.as_str())) {
            (None, None) => source_rows.push([sub, sup]),
            (Some(a), None) => {
                if sup != OWL_THING {
                    types.entry(a).or_default().insert(sup);
                }
            }
            (Some(a), Some(b)) => {
                if a != b {
                    let (low, high) = if a < b { (a, b) } else { (b, a) };
                    same.insert([low.to_string(), high.to_string()]);
                }
            }
            // `C ⊑ {a}`: a fact about the source class, not about `a`.
            (None, Some(_)) => {}
        }
    }
    let unsatisfiable_probe = extended.unsatisfiable.iter().any(|name| is_probe(name));
    extended.unsatisfiable.retain(|name| !is_probe(name));
    extended.subsumptions = source_rows;
    if !extended.consistent {
        return Ok(Realization { classification: extended, types: Vec::new(), same: Vec::new() });
    }
    if unsatisfiable_probe {
        // `{a}` is unsatisfiable only in an inconsistent ontology.
        return Err(OrchestrateError::InvalidOntology(
            "realization: a nominal probe is unsatisfiable in a consistent classification".into(),
        ));
    }

    if mode == TypeMode::Direct {
        let below: HashSet<(&str, &str)> = extended
            .subsumptions
            .iter()
            .map(|[sub, sup]| (sub.as_str(), sup.as_str()))
            .collect();
        let strictly_below = |d: &str, c: &str| below.contains(&(d, c)) && !below.contains(&(c, d));
        for classes in types.values_mut() {
            let direct: BTreeSet<String> = classes
                .iter()
                .filter(|c| !classes.iter().any(|d| strictly_below(d, c)))
                .cloned()
                .collect();
            *classes = direct;
        }
    }
    let types = types
        .into_iter()
        .flat_map(|(a, classes)| classes.into_iter().map(move |c| [a.to_string(), c]))
        .collect();
    Ok(Realization { classification: extended, types, same: same.into_iter().collect() })
}

/// Classify `ont` and realize its named individuals (see the module docs).
///
/// Like `km explain`, realization is answered only under the automatic route
/// policy. A manually forced route may lie outside the fragment it is exact
/// for; on the probe-extended ontology (which always contains nominals) several
/// non-nominal routes are incomplete. `KM_REALIZE_ANY_ROUTE=1` lifts this check
/// for route diagnostics only.
pub fn realize(cfg: &Config, ont: &Path, mode: TypeMode) -> Result<Realization, OrchestrateError> {
    let route = std::env::var("KM_ROUTE").unwrap_or_default();
    if route != crate::routing::Route::Auto.as_str()
        && std::env::var_os(ANY_ROUTE_ENV).is_none()
    {
        return Err(OrchestrateError::OutOfFragment(format!(
            "route {route:?} is not a realization-safe production oracle; use auto"
        )));
    }
    super::validate_user_input(ont)?;
    let prepared = super::input::prepare(ont)?;
    let text = std::fs::read_to_string(prepared.path())?;
    let individuals = source_individuals(&text)?;
    if individuals.is_empty() {
        let classification = super::classify_with_evidence(cfg, ont)?.classification;
        return Ok(Realization { classification, types: Vec::new(), same: Vec::new() });
    }
    let (extended, probes) = probe_source(&text, &individuals)?;
    if std::env::var_os("KM_TIMING").is_some() {
        eprintln!("KM_TIMING realization: {} individual probe(s)", probes.len());
    }
    let rewritten = tmpfile::TempPath::new("-realize.ofn");
    std::fs::write(rewritten.path(), extended)?;
    // The rewrite is the validated source plus declared probe classes whose
    // definitions only name individuals of that source.
    let _trusted = TrustedRewrite::register(rewritten.path());
    let classification = super::classify_with_evidence(cfg, rewritten.path())?.classification;
    split(classification, &probes, mode)
}

impl Realization {
    /// `--lines` output: the classification rows, then `TYPE` and `SAME` rows.
    pub fn to_lines(&self) -> String {
        let mut out = self.classification.to_lines();
        for [a, c] in &self.types {
            out.push_str(&format!("\nTYPE\t{a}\t{c}"));
        }
        for [a, b] in &self.same {
            out.push_str(&format!("\nSAME\t{a}\t{b}"));
        }
        out
    }

    /// JSON output: the classification object with `types` and `same` keys.
    pub fn write_json<W: Write>(&self, writer: W) -> serde_json::Result<()> {
        #[derive(serde::Serialize)]
        struct Encoded<'a> {
            consistent: bool,
            subsumptions: &'a [[String; 2]],
            unsatisfiable: &'a [String],
            dropped: usize,
            types: &'a [[String; 2]],
            same: &'a [[String; 2]],
        }
        let encoded = Encoded {
            consistent: self.classification.consistent,
            subsumptions: &self.classification.subsumptions,
            unsatisfiable: &self.classification.unsatisfiable,
            dropped: self.classification.dropped,
            types: &self.types,
            same: &self.same,
        };
        let mut ser = serde_json::Serializer::with_formatter(writer, super::PyFmt);
        serde::Serialize::serialize(&encoded, &mut ser)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn collects_individuals_in_every_individual_position() {
        let text = "Prefix(:=<urn:t#>)\nOntology(<urn:o>\n\
            Declaration(NamedIndividual(:d))\n\
            Declaration(Class(:C))\n\
            ClassAssertion(Annotation(rdfs:comment \"x\") ObjectSomeValuesFrom(:r ObjectOneOf(:n1 :n2)) :a)\n\
            ObjectPropertyAssertion(:r :a <urn:t#b>)\n\
            NegativeObjectPropertyAssertion(:r :a :c)\n\
            DataPropertyAssertion(:p :e \"1\")\n\
            SameIndividual(:a :f)\n\
            DifferentIndividuals(:g :h)\n\
            SubClassOf(:C ObjectHasValue(:r :v))\n\
            ClassAssertion(:C _:anon)\n\
            AnnotationAssertion(rdfs:label :notind \"x\")\n\
            DLSafeRule(Body(ClassAtom(:C Variable(<urn:x>)) ObjectPropertyAtom(:r Variable(<urn:x>) :w)) Head(ClassAtom(:C :k)))\n\
            )";
        let found = source_individuals(text).unwrap();
        assert_eq!(found, [":d", ":n1", ":n2", ":a", "<urn:t#b>", ":c", ":e", ":f", ":g", ":h", ":v", ":w", ":k"]);
    }

    #[test]
    fn probes_are_inserted_inside_the_ontology_node() {
        let text = "Ontology(<urn:o> ClassAssertion(<urn:C> <urn:a>)) # trailing ) comment\n";
        let individuals = source_individuals(text).unwrap();
        let (extended, probes) = probe_source(text, &individuals).unwrap();
        assert_eq!(probes, [("http://km.invalid/realize#individual0".to_string(), "urn:a".to_string())]);
        assert!(extended.starts_with("Ontology(<urn:o> ClassAssertion(<urn:C> <urn:a>)\n"));
        assert!(extended.contains("EquivalentClasses(<http://km.invalid/realize#individual0> ObjectOneOf(<urn:a>))\n)"));
        assert_eq!(source_individuals(&extended).unwrap(), ["<urn:a>"]);
    }

    #[test]
    fn probe_namespace_avoids_source_iris() {
        assert_eq!(fresh_namespace("<http://km.invalid/realize#x>"), "http://km.invalid/realize1#");
    }

    fn row(a: &str, b: &str) -> [String; 2] {
        [a.to_string(), b.to_string()]
    }

    #[test]
    fn split_separates_types_same_and_source_rows() {
        let probes = vec![("P0".to_string(), "a".to_string()), ("P1".to_string(), "b".to_string())];
        let extended = Classification {
            consistent: true,
            subsumptions: vec![
                row("A", "B"), row("P0", "A"), row("P0", "B"), row("P0", OWL_THING),
                row("P0", "P1"), row("P1", "P0"), row("P1", "A"), row("P1", "B"),
                row("N", "P0"),
            ],
            unsatisfiable: vec!["U".to_string()],
            dropped: 0,
        };
        let all = split(extended.clone(), &probes, TypeMode::All).unwrap();
        assert_eq!(all.classification.subsumptions, [row("A", "B")]);
        assert_eq!(all.classification.unsatisfiable, ["U"]);
        assert_eq!(all.types, [row("a", "A"), row("a", "B"), row("b", "A"), row("b", "B")]);
        assert_eq!(all.same, [row("a", "b")]);
        let direct = split(extended, &probes, TypeMode::Direct).unwrap();
        assert_eq!(direct.types, [row("a", "A"), row("b", "A")]);
    }

    #[test]
    fn direct_types_keep_every_member_of_a_minimal_equivalence_class() {
        let probes = vec![("P0".to_string(), "a".to_string())];
        let extended = Classification {
            consistent: true,
            subsumptions: vec![
                row("A", "A2"), row("A2", "A"), row("A", "B"), row("A2", "B"),
                row("P0", "A"), row("P0", "A2"), row("P0", "B"),
            ],
            unsatisfiable: vec![],
            dropped: 0,
        };
        let direct = split(extended, &probes, TypeMode::Direct).unwrap();
        assert_eq!(direct.types, [row("a", "A"), row("a", "A2")]);
    }

    #[test]
    fn inconsistent_classification_has_no_realization_rows() {
        let probes = vec![("P0".to_string(), "a".to_string())];
        let extended = Classification {
            consistent: false,
            subsumptions: vec![],
            unsatisfiable: vec!["P0".to_string()],
            dropped: 0,
        };
        let result = split(extended, &probes, TypeMode::All).unwrap();
        assert!(!result.classification.consistent);
        assert!(result.classification.unsatisfiable.is_empty());
        assert!(result.types.is_empty() && result.same.is_empty());
    }
}
