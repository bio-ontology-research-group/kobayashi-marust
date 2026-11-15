//! The inferred data property hierarchy, empty and universal data
//! properties, domains and disjoint data properties (W6,
//! `km classify --properties`).
//!
//! # Semantics
//!
//! For a consistent ontology `O` and its named data properties `p`, `q`
//! (other than `owl:topDataProperty` and `owl:bottomDataProperty`):
//!
//! * `SUBDATAPROP p q` iff `O ⊨ p ⊑ q`, `p ≠ q`, `p` not empty;
//! * `TOPDATAPROP p` iff `O ⊨ owl:topDataProperty ⊑ p`;
//! * `BOTDATAPROP p` iff `O ⊨ p ⊑ owl:bottomDataProperty` (no other rows
//!   for `p`, as for object properties);
//! * `DATADOMAIN p C` iff `O ⊨ DataPropertyDomain(p C)`, for a named class
//!   `C` other than `owl:Thing`;
//! * `DISJOINTDATAPROP p q` iff `O ⊨ DisjointDataProperties(p q)`, `p ≠ q`,
//!   both not empty (an empty property is disjoint from every property).
//!
//! # Mechanism
//!
//! One classification of `O` extended with fresh classes. Let `v` be a
//! literal of a fresh datatype read under `--unknown-datatypes=free`: an
//! opaque data value about which `O` says nothing, so in a model of `O` it
//! can be interpreted as any data value. For each `p` KM adds
//! `W_p ≡ ∃p.{v}`, for each pair `p < q` (up to [`MAX_DISJOINT_PROPERTIES`]
//! properties) `X_pq ≡ W_p ⊓ W_q`, and a class `T ≡ owl:Thing`. The
//! extension only defines fresh names, so it is conservative, and:
//!
//! * if `(x, d) ∈ p \ q` in a model of `O`, interpret `v` as `d`: then
//!   `x ∈ W_p \ W_q`; conversely `x ∈ W_p \ W_q` gives `(x, v) ∈ p \ q`. So
//!   `O ⊨ p ⊑ q` iff `O' ⊨ W_p ⊑ W_q`;
//! * `p` is empty iff `W_p` is unsatisfiable, and `W_p ⊑ C` iff
//!   `∃p.⊤ ⊑ C` for a source class `C`;
//! * `(x, d) ∈ p ∩ q` gives `x ∈ W_p ⊓ W_q` for `v = d`, and conversely: `p`
//!   and `q` are disjoint iff `X_pq` is unsatisfiable;
//! * `owl:topDataProperty ⊑ p` iff every element has every value under `p`
//!   iff `O' ⊨ T ⊑ W_p` (`v` arbitrary). (OWL 2 DL admits
//!   `owl:topDataProperty` only as a super-property, so no row is expected.)
//!
//! With more than [`MAX_DISJOINT_PROPERTIES`] data properties the pair
//! probes are left out and the output carries the row `NODATADISJOINT`
//! instead of the `DISJOINTDATAPROP` rows. (Complement probes `¬W_p` would
//! be linear, but they make the CB worker diverge on small inputs with
//! functional data properties; see the round 3 report.)
//!
//! Rows that mention a probe class are removed from the taxonomy, which
//! leaves the classification of `O`. The literal needs the opaque-value
//! reading of the frontend (no membership in any datatype, no equality or
//! inequality with any other literal decided), which KM applies to every
//! literal whose datatype is outside the OWL 2 datatype map.

use std::collections::{BTreeMap, BTreeSet, HashSet};

use crate::frontend::sexpr::Node;

use super::realize::{check_one_spelling, fresh_namespace_for, public_name};
use super::{Classification, OrchestrateError};

const OWL_THING: &str = "http://www.w3.org/2002/07/owl#Thing";

/// The inferred data property rows (see the module docs).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DataPropertyHierarchy {
    pub sub: Vec<[String; 2]>,
    pub top: Vec<String>,
    pub bottom: Vec<String>,
    pub domains: Vec<[String; 2]>,
    pub disjoint: Vec<[String; 2]>,
    /// False when the pair probes were left out (too many properties).
    pub disjoint_computed: bool,
}

impl Default for DataPropertyHierarchy {
    fn default() -> Self {
        DataPropertyHierarchy {
            sub: Vec::new(),
            top: Vec::new(),
            bottom: Vec::new(),
            domains: Vec::new(),
            disjoint: Vec::new(),
            disjoint_computed: true,
        }
    }
}

fn is_builtin_data_property(token: &str) -> bool {
    matches!(
        token,
        "owl:topDataProperty"
            | "owl:bottomDataProperty"
            | "<http://www.w3.org/2002/07/owl#topDataProperty>"
            | "<http://www.w3.org/2002/07/owl#bottomDataProperty>"
    )
}

fn push<'a>(node: Option<&&Node<'a>>, out: &mut Vec<&'a str>) {
    if let Some(Node::Atom(token)) = node.copied() {
        if !token.starts_with('"') {
            out.push(token);
        }
    }
}

fn data_properties_in<'a>(node: &Node<'a>, out: &mut Vec<&'a str>) {
    let Node::List(head, args) = node else { return };
    let plain: Vec<&Node<'a>> = args.iter().filter(|arg| arg.head() != Some("Annotation")).collect();
    match *head {
        "Annotation" | "AnnotationAssertion" | "SubAnnotationPropertyOf"
        | "AnnotationPropertyDomain" | "AnnotationPropertyRange" | "Prefix" | "Import" => {}
        "Declaration" => {
            if let Some(Node::List("DataProperty", inner)) = plain.first().copied() {
                push(inner.first().as_ref(), out);
            }
        }
        // `DataSomeValuesFrom(p1 ... pn D)`: every operand but the last.
        "DataSomeValuesFrom" | "DataAllValuesFrom" => {
            for arg in plain.iter().take(plain.len().saturating_sub(1)) {
                push(Some(arg), out);
            }
        }
        "DataHasValue" | "DataPropertyDomain" | "DataPropertyRange" | "DataPropertyAssertion"
        | "NegativeDataPropertyAssertion" | "DataPropertyAtom" => {
            push(plain.first(), out);
            for arg in plain.iter().skip(1) {
                data_properties_in(arg, out);
            }
        }
        "DataMinCardinality" | "DataMaxCardinality" | "DataExactCardinality" => push(plain.get(1), out),
        "SubDataPropertyOf" | "EquivalentDataProperties" | "DisjointDataProperties"
        | "FunctionalDataProperty" => {
            for arg in &plain {
                push(Some(arg), out);
            }
        }
        "HasKey" => {
            if let Some(class) = plain.first() {
                data_properties_in(class, out);
            }
            if let Some(Node::List("", items)) = plain.get(2).copied() {
                for item in items {
                    push(Some(&item), out);
                }
            }
        }
        _ => {
            for arg in &plain {
                data_properties_in(arg, out);
            }
        }
    }
}

/// The source spelling of every named data property, in first-occurrence
/// order, other than `owl:topDataProperty` and `owl:bottomDataProperty`.
pub fn source_data_properties(text: &str) -> Result<Vec<String>, OrchestrateError> {
    let mut seen: HashSet<&str> = HashSet::new();
    let mut ordered = Vec::new();
    crate::frontend::parse::for_each_ontology_child(text, |node| {
        let mut found = Vec::new();
        data_properties_in(node, &mut found);
        for token in found {
            if !is_builtin_data_property(token) && seen.insert(token) {
                ordered.push(token.to_string());
            }
        }
        Ok(())
    })
    .map_err(|error| OrchestrateError::OutOfFragment(error.0))?;
    Ok(ordered)
}

pub(super) fn canonical_data_properties(canonical: &str) -> Result<Vec<String>, OrchestrateError> {
    let properties = source_data_properties(canonical)?;
    check_one_spelling(canonical, &properties, "property hierarchy: data property")?;
    Ok(properties)
}

/// Pair probes for disjointness are added up to this many data properties.
pub const MAX_DISJOINT_PROPERTIES: usize = 64;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Probe {
    Thing,
    Some(usize),
    Pair(usize, usize),
}

/// The probe classes of one data property extension.
#[derive(Clone, Debug)]
pub struct DataPropertyProbes {
    probes: BTreeMap<String, Probe>,
    names: Vec<String>,
    pairs: bool,
}

impl DataPropertyProbes {
    pub(super) fn is_probe(&self, name: &str) -> bool {
        self.probes.contains_key(name)
    }
}

/// The datatype IRI of the fresh literal of an extension built for `text`.
/// The probe run reads it under `--unknown-datatypes=free`.
pub(super) fn extension(text: &str, properties: &[String]) -> (String, DataPropertyProbes) {
    let ns = fresh_namespace_for(text, "dataproperties");
    let literal = format!("\"v\"^^<{ns}free>");
    let mut out = String::with_capacity(properties.len() * 320 + 128);
    let mut probes = BTreeMap::new();
    let thing = format!("{ns}thing");
    out.push_str(&format!("Declaration(Class(<{thing}>))\nEquivalentClasses(<{thing}> owl:Thing)\n"));
    probes.insert(thing, Probe::Thing);
    let mut names = Vec::with_capacity(properties.len());
    for (index, token) in properties.iter().enumerate() {
        names.push(public_name(token));
        let some = format!("{ns}some{index}");
        out.push_str(&format!(
            "Declaration(Class(<{some}>))\nEquivalentClasses(<{some}> DataHasValue({token} {literal}))\n"
        ));
        probes.insert(some, Probe::Some(index));
    }
    let pairs = properties.len() <= MAX_DISJOINT_PROPERTIES;
    if pairs {
        for p in 0..properties.len() {
            for q in p + 1..properties.len() {
                let pair = format!("{ns}pair{p}_{q}");
                out.push_str(&format!(
                    "Declaration(Class(<{pair}>))\nEquivalentClasses(<{pair}> ObjectIntersectionOf(<{ns}some{p}> <{ns}some{q}>))\n"
                ));
                probes.insert(pair, Probe::Pair(p, q));
            }
        }
    }
    (out, DataPropertyProbes { probes, names, pairs })
}

/// Remove the data property probes from the classification and read the
/// rows off their subsumptions. `foreign` names the probe classes of the
/// other queries.
pub(super) fn split(
    extended: &mut Classification,
    probes: &DataPropertyProbes,
    foreign: &dyn Fn(&str) -> bool,
) -> Result<DataPropertyHierarchy, OrchestrateError> {
    let probe = |name: &str| probes.probes.get(name).copied();
    let unsatisfiable: HashSet<Probe> =
        extended.unsatisfiable.iter().filter_map(|name| probe(name)).collect();
    extended.unsatisfiable.retain(|name| probe(name).is_none());
    let (mut sub, mut top, mut domains, mut disjoint) =
        (BTreeSet::new(), BTreeSet::new(), BTreeSet::new(), BTreeSet::new());
    let mut source_rows = Vec::with_capacity(extended.subsumptions.len());
    for [low, high] in std::mem::take(&mut extended.subsumptions) {
        match (probe(&low), probe(&high)) {
            (None, None) => source_rows.push([low, high]),
            (Some(Probe::Some(p)), Some(Probe::Some(q))) if p != q => {
                sub.insert([probes.names[p].clone(), probes.names[q].clone()]);
            }
            (Some(Probe::Thing), Some(Probe::Some(q))) => {
                top.insert(probes.names[q].clone());
            }
            (Some(Probe::Some(p)), None) if high != OWL_THING && !foreign(&high) => {
                domains.insert([probes.names[p].clone(), high]);
            }
            _ => {}
        }
    }
    extended.subsumptions = source_rows;
    if !extended.consistent {
        return Ok(DataPropertyHierarchy::default());
    }
    if unsatisfiable.contains(&Probe::Thing) {
        return Err(OrchestrateError::InvalidOntology(
            "data property hierarchy: the owl:Thing probe is unsatisfiable in a consistent classification".into(),
        ));
    }
    for probe in &unsatisfiable {
        if let Probe::Pair(p, q) = *probe {
            disjoint.insert([probes.names[p].clone(), probes.names[q].clone()]);
            disjoint.insert([probes.names[q].clone(), probes.names[p].clone()]);
        }
    }
    let bottom: BTreeSet<String> = (0..probes.names.len())
        .filter(|&index| unsatisfiable.contains(&Probe::Some(index)))
        .map(|index| probes.names[index].clone())
        .collect();
    let keep = |row: &[String; 2]| !bottom.contains(&row[0]) && !bottom.contains(&row[1]);
    Ok(DataPropertyHierarchy {
        sub: sub.into_iter().filter(|row| !bottom.contains(&row[0])).collect(),
        top: top.into_iter().collect(),
        domains: domains.into_iter().filter(|row| !bottom.contains(&row[0])).collect(),
        disjoint: disjoint.into_iter().filter(keep).collect(),
        bottom: bottom.into_iter().collect(),
        disjoint_computed: probes.pairs,
    })
}

impl DataPropertyHierarchy {
    /// `--lines` rows, each preceded by a newline.
    pub fn to_lines(&self) -> String {
        let mut out = String::new();
        for [p, q] in &self.sub {
            out.push_str(&format!("\nSUBDATAPROP\t{p}\t{q}"));
        }
        for p in &self.top {
            out.push_str(&format!("\nTOPDATAPROP\t{p}"));
        }
        for p in &self.bottom {
            out.push_str(&format!("\nBOTDATAPROP\t{p}"));
        }
        for [p, c] in &self.domains {
            out.push_str(&format!("\nDATADOMAIN\t{p}\t{c}"));
        }
        for [p, q] in &self.disjoint {
            out.push_str(&format!("\nDISJOINTDATAPROP\t{p}\t{q}"));
        }
        if !self.disjoint_computed {
            out.push_str("\nNODATADISJOINT");
        }
        out
    }
}
