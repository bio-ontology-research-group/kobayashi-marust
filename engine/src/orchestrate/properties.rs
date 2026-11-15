//! The inferred object property hierarchy, with domains and ranges
//! (`km classify --properties`).
//!
//! # Semantics
//!
//! Let `O` be a consistent ontology. The object property expressions are the
//! named object properties `r` of the source signature (other than
//! `owl:topObjectProperty` and `owl:bottomObjectProperty`) and their inverses
//! `ObjectInverseOf(r)`. KM reports:
//!
//! * `SUBPROP r f` iff `O ⊨ r ⊑ f`, for a named `r`, an expression `f ≠ r`,
//!   and `r` not empty. A pair with an inverse on the left is reported through
//!   its mirror: `O ⊨ r⁻ ⊑ f` iff `O ⊨ r ⊑ f⁻`. Equivalent properties have
//!   rows in both directions, and `s` is an inverse of `r` iff
//!   `SUBPROP r ObjectInverseOf(s)` and `SUBPROP s ObjectInverseOf(r)`.
//!   `owl:topObjectProperty` is never listed, as `owl:Thing` is never listed
//!   in the class rows.
//! * `TOPPROP r` iff `O ⊨ owl:topObjectProperty ⊑ r`.
//! * `BOTPROP r` iff `O ⊨ r ⊑ owl:bottomObjectProperty`. An empty property
//!   has no `SUBPROP`, `DOMAIN` or `RANGE` rows: it is below every property
//!   and has every class as domain and range, so the rows would carry no
//!   information, and the classification reports the `SUB` rows of an
//!   unsatisfiable class only partially (route-dependent).
//! * `DOMAIN r C` iff `O ⊨ ∃r.⊤ ⊑ C` and `RANGE r C` iff `O ⊨ ∃r⁻.⊤ ⊑ C`, for
//!   a named class `C` other than `owl:Thing`, in the closure convention of
//!   the `SUB` rows of `∃r.⊤` and `∃r⁻.⊤`.
//!
//! For an inconsistent ontology the classification reports `CONSISTENT 0` and
//! no property rows are written.
//!
//! # Mechanism
//!
//! The reduction to classification with fresh names, as for realization. Let
//! `B` be a fresh class. For each expression `e` KM adds a fresh class
//! `P_e ≡ ∃e.B`. The extension only defines fresh names, so it is
//! conservative. Because `B` is fresh it can be interpreted as any set, in
//! particular a singleton `{y}` or the whole domain:
//!
//! * if `(x, y) ∈ e \ f` in a model of `O`, set `B = {y}`: then
//!   `x ∈ P_e \ P_f`; conversely `x ∈ P_e \ P_f` gives a `y ∈ B` with
//!   `(x, y) ∈ e \ f`. So `O ⊨ e ⊑ f` iff `O' ⊨ P_e ⊑ P_f`;
//! * `e` is empty iff `P_e` is unsatisfiable;
//! * `P_r ⊑ C` iff `∃r.⊤ ⊑ C` for a source class `C`, so the domains of `r`
//!   are the named superclasses of `P_r`, and the ranges those of `P_{r⁻}`.
//!
//! The probes depend on the source (plan section 12, [`SourceShape`]):
//!
//! * `P_⊤ ≡ ∃owl:topObjectProperty.B` (`owl:topObjectProperty ⊑ f` iff
//!   `P_⊤ ⊑ P_f`) only when the source uses `owl:topObjectProperty` or an
//!   object nominal. Otherwise every model has a disjoint union with an
//!   individual-free copy of itself, which is a model in which no named
//!   property relates the two parts, so no named property is universal.
//! * On an inverse-free source no `P_{r⁻}` is added. Unravel a model into a
//!   forest from the named individuals: an `r`-edge to a child has no edge
//!   back, so a nonempty named `r` is below no inverse `s⁻`, and there are no
//!   inverse rows. The ranges then come from a second classification, of the
//!   source with fresh asserted pairs `r(a_r, b_r)` for the nonempty `r`
//!   ([`range_extension`]).
//!
//! One classification of `O'` answers the rest; rows that mention a probe
//! class are removed from the taxonomy, which leaves the classification of
//! `O`.

use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::io::Write;

use crate::frontend::sexpr::Node;

use super::realize::{check_one_spelling, fresh_namespace_for, public_name};
use super::{Classification, OrchestrateError};

const OWL_THING: &str = "http://www.w3.org/2002/07/owl#Thing";

/// The inferred object property rows of an ontology (see the module docs).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct PropertyHierarchy {
    /// `[r, f]` rows: `r ⊑ f`, `r` named and not empty, sorted.
    pub sub: Vec<[String; 2]>,
    /// Named properties equivalent to `owl:topObjectProperty`, sorted.
    pub top: Vec<String>,
    /// Named properties equivalent to `owl:bottomObjectProperty`, sorted.
    pub bottom: Vec<String>,
    /// `[r, C]` rows: `C` is a domain of `r`, sorted.
    pub domains: Vec<[String; 2]>,
    /// `[r, C]` rows: `C` is a range of `r`, sorted.
    pub ranges: Vec<[String; 2]>,
}

fn is_builtin_property(token: &str) -> bool {
    matches!(
        token,
        "owl:topObjectProperty"
            | "owl:bottomObjectProperty"
            | "<http://www.w3.org/2002/07/owl#topObjectProperty>"
            | "<http://www.w3.org/2002/07/owl#bottomObjectProperty>"
    )
}

/// The source spelling of every named object property of an OFN document,
/// in first-occurrence order and without duplicates, other than
/// `owl:topObjectProperty` and `owl:bottomObjectProperty`.
///
/// Object properties are the declared ones and those in object property
/// position of class expressions, property axioms, assertions, `HasKey` and
/// DL-safe rule atoms. The OFN syntax tells object and data properties
/// apart by position, so no data property is collected.
pub fn source_object_properties(text: &str) -> Result<Vec<String>, OrchestrateError> {
    let mut seen: HashSet<&str> = HashSet::new();
    let mut ordered: Vec<String> = Vec::new();
    crate::frontend::parse::for_each_ontology_child(text, |node| {
        let mut found = Vec::new();
        properties_in(node, &mut found);
        for token in found {
            if !is_builtin_property(token) && seen.insert(token) {
                ordered.push(token.to_string());
            }
        }
        Ok(())
    })
    .map_err(|error| OrchestrateError::OutOfFragment(error.0))?;
    Ok(ordered)
}

/// An object property expression: a name or `ObjectInverseOf(name)`.
fn push_property<'a>(node: Option<&&Node<'a>>, out: &mut Vec<&'a str>) {
    match node.copied() {
        Some(Node::Atom(token)) if !token.starts_with('"') => out.push(token),
        Some(Node::List("ObjectInverseOf", inner)) => push_property(inner.first().as_ref(), out),
        _ => {}
    }
}

fn properties_in<'a>(node: &Node<'a>, out: &mut Vec<&'a str>) {
    let Node::List(head, args) = node else { return };
    let plain: Vec<&Node<'a>> = args
        .iter()
        .filter(|arg| arg.head() != Some("Annotation"))
        .collect();
    let rest = |from: usize, out: &mut Vec<&'a str>| {
        for arg in plain.iter().skip(from) {
            properties_in(arg, out);
        }
    };
    match *head {
        "Annotation" | "AnnotationAssertion" | "SubAnnotationPropertyOf"
        | "AnnotationPropertyDomain" | "AnnotationPropertyRange" | "Prefix" | "Import" => {}
        "Declaration" => {
            if let Some(Node::List("ObjectProperty", inner)) = plain.first().copied() {
                push_property(inner.first().as_ref(), out);
            }
        }
        "ObjectSomeValuesFrom" | "ObjectAllValuesFrom" | "ObjectHasValue" | "ObjectHasSelf"
        | "ObjectPropertyDomain" | "ObjectPropertyRange" | "ObjectPropertyAssertion"
        | "NegativeObjectPropertyAssertion" | "ObjectPropertyAtom" => {
            push_property(plain.first(), out);
            rest(1, out);
        }
        "ObjectMinCardinality" | "ObjectMaxCardinality" | "ObjectExactCardinality" => {
            push_property(plain.get(1), out);
            rest(2, out);
        }
        "SubObjectPropertyOf" | "EquivalentObjectProperties" | "DisjointObjectProperties"
        | "InverseObjectProperties" | "ObjectPropertyChain" | "FunctionalObjectProperty"
        | "InverseFunctionalObjectProperty" | "ReflexiveObjectProperty"
        | "IrreflexiveObjectProperty" | "SymmetricObjectProperty"
        | "AsymmetricObjectProperty" | "TransitiveObjectProperty" | "ObjectInverseOf" => {
            for arg in &plain {
                match arg {
                    Node::List("ObjectPropertyChain", _) => properties_in(arg, out),
                    _ => push_property(Some(arg), out),
                }
            }
        }
        "HasKey" => {
            // `HasKey(C (ope*) (dpe*))`: the first bare list holds the object
            // property expressions.
            if let Some(class) = plain.first() {
                properties_in(class, out);
            }
            if let Some(Node::List("", items)) = plain.get(1).copied() {
                for item in items {
                    push_property(Some(&item), out);
                }
            }
        }
        // Data property axioms, data ranges and the remaining rule atoms name
        // no object property; class expressions inside them are visited.
        _ => rest(0, out),
    }
}

/// What the reduction needs to know about the source (plan section 12).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(super) struct SourceShape {
    /// The source uses `owl:topObjectProperty` other than as the super-role of
    /// a `SubObjectPropertyOf` tautology, or an object nominal (`ObjectOneOf`,
    /// `ObjectHasValue`). Otherwise every model has a disjoint union with an
    /// individual-free copy of itself, so no named property is universal and
    /// `P_⊤` is not needed.
    pub universal_possible: bool,
    /// No inverse role can be entailed above a nonempty named property, and
    /// fresh asserted pairs do not interact: no `ObjectInverseOf`,
    /// `InverseObjectProperties`, symmetric, inverse functional or reflexive
    /// property, `ObjectHasSelf`, object nominal or `owl:topObjectProperty`
    /// (beyond the tautology above), and no `DLSafeRule` or `HasKey`, whose
    /// named-individual semantics would also apply to the fresh individuals
    /// of the range run.
    pub inverse_free: bool,
}

fn is_universal_property(token: &str) -> bool {
    matches!(token, "owl:topObjectProperty" | "<http://www.w3.org/2002/07/owl#topObjectProperty>")
}

fn mentions_universal_property(node: &Node<'_>) -> bool {
    match node {
        Node::Atom(token) => is_universal_property(token),
        Node::List("Annotation", _) => false,
        Node::List(_, args) => args.iter().any(mentions_universal_property),
    }
}

/// Collect the shape facts of one logical node (annotations are skipped).
fn shape_in(node: &Node<'_>, universal: &mut bool, inverse: &mut bool) {
    let Node::List(head, args) = node else {
        if let Node::Atom(token) = node {
            if is_universal_property(token) {
                *universal = true;
                *inverse = true;
            }
        }
        return;
    };
    match *head {
        "Annotation" | "AnnotationAssertion" | "SubAnnotationPropertyOf"
        | "AnnotationPropertyDomain" | "AnnotationPropertyRange" | "Declaration" => return,
        "SubObjectPropertyOf" => {
            let plain: Vec<&Node<'_>> =
                args.iter().filter(|arg| arg.head() != Some("Annotation")).collect();
            // `R ⊑ U` holds in every interpretation (see `frontend::top_role`).
            if let [sub, Node::Atom(sup)] = plain.as_slice() {
                if is_universal_property(sup) && !mentions_universal_property(sub) {
                    shape_in(sub, universal, inverse);
                    return;
                }
            }
        }
        "ObjectOneOf" | "ObjectHasValue" => {
            *universal = true;
            *inverse = true;
        }
        "ObjectInverseOf" | "InverseObjectProperties" | "SymmetricObjectProperty"
        | "InverseFunctionalObjectProperty" | "ReflexiveObjectProperty" | "ObjectHasSelf"
        | "DLSafeRule" | "HasKey" => *inverse = true,
        _ => {}
    }
    for arg in args {
        shape_in(arg, universal, inverse);
    }
}

/// The [`SourceShape`] of the canonical source, decided syntactically on the
/// document km parses (km resolves no imports).
pub(super) fn source_shape(canonical: &str) -> Result<SourceShape, OrchestrateError> {
    let mut universal = false;
    let mut inverse = false;
    crate::frontend::parse::for_each_ontology_child(canonical, |node| {
        shape_in(node, &mut universal, &mut inverse);
        Ok(())
    })
    .map_err(|error| OrchestrateError::OutOfFragment(error.0))?;
    Ok(SourceShape { universal_possible: universal, inverse_free: !inverse })
}

/// The named object properties of the canonical source (see
/// `realize::canonical_individuals` for the spelling invariant).
pub(super) fn canonical_properties(canonical: &str) -> Result<Vec<String>, OrchestrateError> {
    let properties = source_object_properties(canonical)?;
    check_one_spelling(canonical, &properties, "property hierarchy: object property")?;
    Ok(properties)
}

/// What a probe class stands for.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Probe {
    /// The fresh filler `B`.
    Filler,
    /// `∃owl:topObjectProperty.B`.
    Top,
    /// `∃e.B` for the expression `e` (index into the expression names).
    Some(usize),
}

/// The probe classes of one extension.
#[derive(Clone, Debug)]
pub struct PropertyProbes {
    /// Probe IRI (as the output spells it) to what it stands for.
    probes: BTreeMap<String, Probe>,
    /// Public names: `2 i` is the named property `i`, `2 i + 1` its inverse.
    expressions: Vec<String>,
    /// Source spellings of the named properties.
    tokens: Vec<String>,
    /// The shape the extension was built for.
    shape: SourceShape,
}

impl PropertyProbes {
    fn named(&self, index: usize) -> &str {
        &self.expressions[2 * index]
    }

    /// Is `name` one of these probe classes?
    pub(super) fn is_probe(&self, name: &str) -> bool {
        self.probes.contains_key(name)
    }

    /// Ranges come from a second run with asserted pairs (plan 12, item 4).
    pub(super) fn ranges_by_assertion(&self) -> bool {
        self.shape.inverse_free
    }
}

/// The probe axioms for `properties` (source spellings) and their probes.
///
/// `P_e ≡ ∃e.B` for every named property, and for its inverse unless the
/// source is inverse-free; `P_⊤ ≡ ∃owl:topObjectProperty.B` only when a
/// universal named property is possible (see [`SourceShape`]).
pub(super) fn extension(text: &str, properties: &[String], shape: SourceShape) -> (String, PropertyProbes) {
    let ns = fresh_namespace_for(text, "properties");
    let mut out = String::with_capacity(properties.len() * 256 + 256);
    let mut probes = BTreeMap::new();
    let mut expressions = Vec::with_capacity(properties.len() * 2);
    let filler = format!("{ns}filler");
    out.push_str(&format!("Declaration(Class(<{filler}>))\n"));
    probes.insert(filler.clone(), Probe::Filler);
    if shape.universal_possible {
        let top = format!("{ns}top");
        out.push_str(&format!(
            "Declaration(Class(<{top}>))\nEquivalentClasses(<{top}> ObjectSomeValuesFrom(owl:topObjectProperty <{filler}>))\n"
        ));
        probes.insert(top, Probe::Top);
    }
    for (index, token) in properties.iter().enumerate() {
        let name = public_name(token);
        expressions.push(name.clone());
        expressions.push(format!("ObjectInverseOf({name})"));
        let inverse = format!("ObjectInverseOf({token})");
        let both = [token.as_str(), inverse.as_str()];
        let wanted = if shape.inverse_free { &both[..1] } else { &both[..] };
        for (offset, expression) in wanted.iter().enumerate() {
            let probe = format!("{ns}some{}", 2 * index + offset);
            out.push_str(&format!(
                "Declaration(Class(<{probe}>))\nEquivalentClasses(<{probe}> ObjectSomeValuesFrom({expression} <{filler}>))\n"
            ));
            probes.insert(probe, Probe::Some(2 * index + offset));
        }
    }
    (out, PropertyProbes { probes, expressions, tokens: properties.to_vec(), shape })
}

/// The range run of an inverse-free source (plan 12, item 4): one fresh pair
/// `r(a_r, b_r)` per nonempty named property `r`. Returns the assertions and,
/// per asserted property, the source spelling of `b_r`.
///
/// Soundness: `O ⊨ ∃r⁻.⊤ ⊑ C` iff `O ∪ {r(a, b)} ⊨ C(b)` for fresh `a`, `b`
/// (a model of `O` with an `r`-edge into `¬C` interprets `a`, `b` on it, and
/// conversely). All pairs go into one ontology: for each `r` take such a
/// model of `O`; the disjoint union of these models, with the source
/// individuals interpreted in one of them, is a model of `O` (no nominals),
/// and the fresh individuals do not meet any key or rule (none in an
/// inverse-free source). So each `b_r` has exactly the types it has alone.
pub(super) fn range_extension(
    text: &str,
    probes: &PropertyProbes,
    hierarchy: &PropertyHierarchy,
) -> (String, Vec<(usize, String)>) {
    let ns = fresh_namespace_for(text, "ranges");
    let empty: HashSet<&str> = hierarchy.bottom.iter().map(String::as_str).collect();
    let mut out = String::from("\n");
    let mut pairs = Vec::new();
    for (index, token) in probes.tokens.iter().enumerate() {
        if empty.contains(probes.named(index)) {
            continue;
        }
        let a = format!("<{ns}a{index}>");
        let b = format!("<{ns}b{index}>");
        out.push_str(&format!(
            "Declaration(NamedIndividual({a}))\nDeclaration(NamedIndividual({b}))\nObjectPropertyAssertion({token} {a} {b})\n"
        ));
        pairs.push((index, b));
    }
    (out, pairs)
}

/// `RANGE` rows from the named types of the fresh range individuals.
pub(super) fn ranges_from_types(
    probes: &PropertyProbes,
    pairs: &[(usize, String)],
    types: &[[String; 2]],
) -> Vec<[String; 2]> {
    let property_of: BTreeMap<String, usize> =
        pairs.iter().map(|(index, b)| (public_name(b), *index)).collect();
    let mut ranges = BTreeSet::new();
    for [individual, class] in types {
        if let Some(&index) = property_of.get(individual) {
            if class != OWL_THING {
                ranges.insert([probes.named(index).to_string(), class.clone()]);
            }
        }
    }
    ranges.into_iter().collect()
}

/// Remove the property probes from the classification of the extended
/// ontology and read the property rows off their subsumptions. `foreign`
/// names the probe classes of other queries (realization): a row between one
/// of them and a property probe is dropped, and rows without a property probe
/// are left for their own split.
pub(super) fn split(
    extended: &mut Classification,
    probes: &PropertyProbes,
    foreign: &dyn Fn(&str) -> bool,
) -> Result<PropertyHierarchy, OrchestrateError> {
    let probe = |name: &str| probes.probes.get(name).copied();
    let unsatisfiable: HashSet<Probe> = extended
        .unsatisfiable
        .iter()
        .filter_map(|name| probe(name))
        .collect();
    extended.unsatisfiable.retain(|name| probe(name).is_none());
    let mut sub = BTreeSet::new();
    let mut top = BTreeSet::new();
    let mut domains = BTreeSet::new();
    let mut ranges = BTreeSet::new();
    let mut source_rows = Vec::with_capacity(extended.subsumptions.len());
    for [low, high] in std::mem::take(&mut extended.subsumptions) {
        match (probe(&low), probe(&high)) {
            (None, None) => source_rows.push([low, high]),
            (Some(Probe::Some(e)), Some(Probe::Some(f))) if e % 2 == 0 && e != f => {
                sub.insert([probes.expressions[e].clone(), probes.expressions[f].clone()]);
            }
            (Some(Probe::Top), Some(Probe::Some(f))) if f % 2 == 0 => {
                top.insert(probes.expressions[f].clone());
            }
            // `∃r.B ⊑ C` iff `∃r.⊤ ⊑ C`, because `B` is fresh: the domains.
            (Some(Probe::Some(e)), None) if high != OWL_THING && !foreign(&high) => {
                let row = [probes.named(e / 2).to_string(), high];
                if e % 2 == 0 {
                    domains.insert(row);
                } else {
                    ranges.insert(row);
                }
            }
            // Mirrors of reported pairs and facts about source classes or
            // individual probes.
            _ => {}
        }
    }
    extended.subsumptions = source_rows;
    if !extended.consistent {
        return Ok(PropertyHierarchy::default());
    }
    if unsatisfiable.contains(&Probe::Filler) || unsatisfiable.contains(&Probe::Top) {
        return Err(OrchestrateError::InvalidOntology(
            "property hierarchy: a fresh probe is unsatisfiable in a consistent classification".into(),
        ));
    }
    let mut bottom: BTreeSet<String> = BTreeSet::new();
    for index in 0..probes.expressions.len() / 2 {
        let checked: &[Probe] = if probes.shape.inverse_free {
            &[Probe::Some(2 * index)]
        } else {
            &[Probe::Some(2 * index), Probe::Some(2 * index + 1)]
        };
        let empty: Vec<bool> = checked.iter().map(|p| unsatisfiable.contains(p)).collect();
        if empty.iter().any(|&e| e) != empty.iter().all(|&e| e) {
            // `∃r.B` and `∃r⁻.B` are empty together in every model.
            return Err(OrchestrateError::InvalidOntology(format!(
                "property hierarchy: the probes of {} disagree on its emptiness",
                probes.named(index)
            )));
        }
        if empty[0] {
            bottom.insert(probes.named(index).to_string());
        }
    }
    let mut domains: Vec<[String; 2]> = domains.into_iter().collect();
    let mut ranges: Vec<[String; 2]> = ranges.into_iter().collect();
    let mut sub: Vec<[String; 2]> = sub.into_iter().collect();
    sub.retain(|[r, _]| !bottom.contains(r));
    domains.retain(|[r, _]| !bottom.contains(r));
    ranges.retain(|[r, _]| !bottom.contains(r));
    Ok(PropertyHierarchy {
        sub,
        top: top.into_iter().collect(),
        bottom: bottom.into_iter().collect(),
        domains,
        ranges,
    })
}

impl PropertyHierarchy {
    /// `--lines` rows, each preceded by a newline.
    pub fn to_lines(&self) -> String {
        let mut out = String::new();
        for [r, f] in &self.sub {
            out.push_str(&format!("\nSUBPROP\t{r}\t{f}"));
        }
        for r in &self.top {
            out.push_str(&format!("\nTOPPROP\t{r}"));
        }
        for r in &self.bottom {
            out.push_str(&format!("\nBOTPROP\t{r}"));
        }
        for [r, c] in &self.domains {
            out.push_str(&format!("\nDOMAIN\t{r}\t{c}"));
        }
        for [r, c] in &self.ranges {
            out.push_str(&format!("\nRANGE\t{r}\t{c}"));
        }
        out
    }
}

impl super::realize::Extended {
    /// `--lines` output: the classification rows, then the `TOP` rows (with
    /// `--top`), the realization rows (with `--realize`) and the property
    /// rows (with `--properties`).
    pub fn to_lines(&self) -> String {
        let mut out = self.realization.classification.to_lines();
        for class in self.top.iter().flatten() {
            out.push_str(&format!("\nTOP\t{class}"));
        }
        for [a, c] in &self.realization.types {
            out.push_str(&format!("\nTYPE\t{a}\t{c}"));
        }
        for [a, b] in &self.realization.same {
            out.push_str(&format!("\nSAME\t{a}\t{b}"));
        }
        if let Some(properties) = &self.properties {
            out.push_str(&properties.to_lines());
        }
        if let Some(data) = &self.data_properties {
            out.push_str(&data.to_lines());
        }
        for [r, a, b] in self.abox.values.iter().flatten() {
            out.push_str(&format!("\nVALUE\t{r}\t{a}\t{b}"));
        }
        for [a, b] in self.abox.different.iter().flatten() {
            out.push_str(&format!("\nDIFFERENT\t{a}\t{b}"));
        }
        out
    }

    /// JSON output: the classification object, with a `top` key with
    /// `--top`, `types` and `same` keys when `realized`, and `subproperties`, `topproperties`,
    /// `bottomproperties`, `domains` and `ranges` with `--properties`.
    pub fn write_json<W: Write>(&self, writer: W, realized: bool) -> serde_json::Result<()> {
        #[derive(serde::Serialize)]
        struct Encoded<'a> {
            consistent: bool,
            subsumptions: &'a [[String; 2]],
            unsatisfiable: &'a [String],
            dropped: usize,
            #[serde(skip_serializing_if = "Option::is_none")]
            approximate: Option<&'a str>,
            #[serde(skip_serializing_if = "Option::is_none")]
            top: Option<&'a [String]>,
            #[serde(skip_serializing_if = "Option::is_none")]
            types: Option<&'a [[String; 2]]>,
            #[serde(skip_serializing_if = "Option::is_none")]
            same: Option<&'a [[String; 2]]>,
            #[serde(skip_serializing_if = "Option::is_none")]
            subproperties: Option<&'a [[String; 2]]>,
            #[serde(skip_serializing_if = "Option::is_none")]
            topproperties: Option<&'a [String]>,
            #[serde(skip_serializing_if = "Option::is_none")]
            bottomproperties: Option<&'a [String]>,
            #[serde(skip_serializing_if = "Option::is_none")]
            domains: Option<&'a [[String; 2]]>,
            #[serde(skip_serializing_if = "Option::is_none")]
            ranges: Option<&'a [[String; 2]]>,
            #[serde(skip_serializing_if = "Option::is_none")]
            subdataproperties: Option<&'a [[String; 2]]>,
            #[serde(skip_serializing_if = "Option::is_none")]
            topdataproperties: Option<&'a [String]>,
            #[serde(skip_serializing_if = "Option::is_none")]
            bottomdataproperties: Option<&'a [String]>,
            #[serde(skip_serializing_if = "Option::is_none")]
            datadomains: Option<&'a [[String; 2]]>,
            #[serde(skip_serializing_if = "Option::is_none")]
            disjointdataproperties: Option<&'a [[String; 2]]>,
            #[serde(skip_serializing_if = "Option::is_none")]
            values: Option<&'a [[String; 3]]>,
            #[serde(skip_serializing_if = "Option::is_none")]
            different: Option<&'a [[String; 2]]>,
        }
        let c = &self.realization.classification;
        let p = self.properties.as_ref();
        let encoded = Encoded {
            consistent: c.consistent,
            subsumptions: &c.subsumptions,
            unsatisfiable: &c.unsatisfiable,
            dropped: c.dropped,
            approximate: c.approximate.as_deref(),
            top: self.top.as_deref(),
            types: realized.then_some(self.realization.types.as_slice()),
            same: realized.then_some(self.realization.same.as_slice()),
            subproperties: p.map(|p| p.sub.as_slice()),
            topproperties: p.map(|p| p.top.as_slice()),
            bottomproperties: p.map(|p| p.bottom.as_slice()),
            domains: p.map(|p| p.domains.as_slice()),
            ranges: p.map(|p| p.ranges.as_slice()),
            subdataproperties: self.data_properties.as_ref().map(|d| d.sub.as_slice()),
            topdataproperties: self.data_properties.as_ref().map(|d| d.top.as_slice()),
            bottomdataproperties: self.data_properties.as_ref().map(|d| d.bottom.as_slice()),
            datadomains: self.data_properties.as_ref().map(|d| d.domains.as_slice()),
            disjointdataproperties: self.data_properties.as_ref().map(|d| d.disjoint.as_slice()),
            values: self.abox.values.as_deref(),
            different: self.abox.different.as_deref(),
        };
        let mut ser = serde_json::Serializer::with_formatter(writer, super::PyFmt);
        serde::Serialize::serialize(&encoded, &mut ser)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn collects_object_properties_in_every_position() {
        let _test_env = crate::test_env::write();
        let text = "Prefix(:=<urn:t#>)\nOntology(<urn:o>\n\
            Declaration(ObjectProperty(:d))\n\
            Declaration(DataProperty(:dp))\n\
            SubClassOf(:A ObjectSomeValuesFrom(:a ObjectAllValuesFrom(ObjectInverseOf(:b) :C)))\n\
            SubClassOf(:A ObjectMinCardinality(2 :c ObjectHasSelf(:e)))\n\
            SubClassOf(:A DataSomeValuesFrom(:dq xsd:integer))\n\
            SubObjectPropertyOf(ObjectPropertyChain(:f ObjectInverseOf(:g)) owl:topObjectProperty)\n\
            InverseObjectProperties(:h :i)\n\
            TransitiveObjectProperty(Annotation(rdfs:comment \"x\") :j)\n\
            ObjectPropertyAssertion(:k :x :y)\n\
            HasKey(:A (:l ObjectInverseOf(:m)) (:dk))\n\
            SubClassOf(:A ObjectHasValue(owl:bottomObjectProperty :x))\n\
            DLSafeRule(Body(ObjectPropertyAtom(:n Variable(<urn:x>) :w)) Head(ClassAtom(ObjectSomeValuesFrom(:o :C) :k)))\n\
            AnnotationAssertion(rdfs:label :p \"x\")\n\
            )";
        let found = source_object_properties(text).unwrap();
        assert_eq!(found, [":d", ":a", ":b", ":c", ":e", ":f", ":g", ":h", ":i", ":j", ":k", ":l", ":m", ":n", ":o"]);
    }

    const GENERAL: SourceShape = SourceShape { universal_possible: true, inverse_free: false };
    const INVERSE_FREE: SourceShape = SourceShape { universal_possible: false, inverse_free: true };

    #[test]
    fn extension_defines_every_probe() {
        let _test_env = crate::test_env::write();
        let text = "Ontology(<urn:o> SubObjectPropertyOf(<urn:r> <urn:s>))";
        let roles = source_object_properties(text).unwrap();
        let (extension, probes) = extension(text, &roles, GENERAL);
        assert_eq!(probes.expressions, ["urn:r", "ObjectInverseOf(urn:r)", "urn:s", "ObjectInverseOf(urn:s)"]);
        let ns = "http://km.invalid/properties#";
        for line in [
            format!("EquivalentClasses(<{ns}top> ObjectSomeValuesFrom(owl:topObjectProperty <{ns}filler>))"),
            format!("EquivalentClasses(<{ns}some0> ObjectSomeValuesFrom(<urn:r> <{ns}filler>))"),
            format!("EquivalentClasses(<{ns}some1> ObjectSomeValuesFrom(ObjectInverseOf(<urn:r>) <{ns}filler>))"),
        ] {
            assert!(extension.contains(&line), "{line}");
        }
        assert!(!extension.contains("owl:Thing"), "{extension}");
        assert_eq!(probes.probes.len(), 2 + 2 * 2);
        // Inverse-free: no inverse probes and no universal-role probe.
        let (extension, probes) = super::extension(text, &roles, INVERSE_FREE);
        assert!(!extension.contains("ObjectInverseOf"), "{extension}");
        assert!(!extension.contains("topObjectProperty"), "{extension}");
        assert_eq!(probes.probes.len(), 1 + 2);
        assert!(probes.ranges_by_assertion());
    }

    #[test]
    fn source_shape_follows_the_plan() {
        let _test_env = crate::test_env::write();
        let shape = |body: &str| source_shape(&format!("Prefix(:=<urn:t#>) Ontology({body})")).unwrap();
        let free = shape("SubObjectPropertyOf(:r :s) ObjectPropertyRange(:r :A) \
            SubObjectPropertyOf(:s owl:topObjectProperty) TransitiveObjectProperty(:r) \
            FunctionalObjectProperty(:r) SubClassOf(:A ObjectMaxCardinality(1 :r :B)) \
            ClassAssertion(:A :a) ObjectPropertyAssertion(:r :a :b) \
            AnnotationAssertion(rdfs:comment :A \"ObjectInverseOf ObjectOneOf\")");
        assert_eq!(free, INVERSE_FREE);
        for body in ["SubClassOf(:A ObjectSomeValuesFrom(ObjectInverseOf(:r) :B))",
            "InverseObjectProperties(:r :s)", "SymmetricObjectProperty(:r)",
            "InverseFunctionalObjectProperty(:r)", "ReflexiveObjectProperty(:r)",
            "SubClassOf(:A ObjectHasSelf(:r))",
            "DLSafeRule(Body(ClassAtom(:A Variable(<urn:x>))) Head(ClassAtom(:B Variable(<urn:x>))))",
            "HasKey(:A (:r) ())"] {
            assert_eq!(shape(body), SourceShape { universal_possible: false, inverse_free: false }, "{body}");
        }
        for body in ["SubClassOf(:A ObjectOneOf(:a))", "SubClassOf(:A ObjectHasValue(:r :a))",
            "SubObjectPropertyOf(owl:topObjectProperty :r)",
            "SubClassOf(:A ObjectAllValuesFrom(owl:topObjectProperty :B))"] {
            assert_eq!(shape(body), SourceShape { universal_possible: true, inverse_free: false }, "{body}");
        }
    }

    fn row(a: &str, b: &str) -> [String; 2] {
        [a.to_string(), b.to_string()]
    }

    fn probes() -> PropertyProbes {
        let text = "Ontology(<urn:o> SubObjectPropertyOf(<urn:r> <urn:s>) ObjectPropertyDomain(<urn:e> owl:Nothing))";
        let roles = source_object_properties(text).unwrap();
        extension(text, &roles, GENERAL).1
    }

    #[test]
    fn split_reads_property_rows_and_keeps_source_rows() {
        let _test_env = crate::test_env::write();
        let ns = "http://km.invalid/properties#";
        let p = |name: &str| format!("{ns}{name}");
        // r = 0 (some0, some1), s = 1 (some2, some3), e = 2 (some4, some5).
        let mut extended = Classification {
            approximate: None,
            consistent: true,
            subsumptions: vec![
                row("A", "B"),
                row(&p("some0"), &p("some2")),
                row(&p("some1"), &p("some3")),
                row(&p("some2"), &p("some3")),
                row(&p("top"), &p("some2")),
                row(&p("top"), &p("some3")),
                row(&p("some0"), "A"),
                row(&p("some0"), OWL_THING),
                row(&p("some1"), "B"),
                row(&p("some4"), "T"),
                row(&p("some0"), "foreign"),
                row("A", &p("some0")),
            ],
            unsatisfiable: vec!["U".into(), p("some4"), p("some5")],
            dropped: 0,
        };
        let hierarchy = split(&mut extended, &probes(), &|name| name == "foreign").unwrap();
        assert_eq!(extended.subsumptions, [row("A", "B")]);
        assert_eq!(extended.unsatisfiable, ["U"]);
        assert_eq!(hierarchy.sub, [row("urn:r", "urn:s"), row("urn:s", "ObjectInverseOf(urn:s)")]);
        assert_eq!(hierarchy.top, ["urn:s"]);
        assert_eq!(hierarchy.bottom, ["urn:e"]);
        assert_eq!(hierarchy.domains, [row("urn:r", "A")]);
        assert_eq!(hierarchy.ranges, [row("urn:r", "B")]);
        let lines = hierarchy.to_lines();
        assert_eq!(
            lines,
            "\nSUBPROP\turn:r\turn:s\nSUBPROP\turn:s\tObjectInverseOf(urn:s)\nTOPPROP\turn:s\
             \nBOTPROP\turn:e\nDOMAIN\turn:r\tA\nRANGE\turn:r\tB"
        );
    }

    #[test]
    fn range_run_asserts_one_pair_per_nonempty_property() {
        let _test_env = crate::test_env::write();
        let text = "Ontology(<urn:o> SubObjectPropertyOf(<urn:r> <urn:s>) ObjectPropertyDomain(<urn:e> owl:Nothing))";
        let roles = source_object_properties(text).unwrap();
        let (_, probes) = extension(text, &roles, INVERSE_FREE);
        let hierarchy = PropertyHierarchy { bottom: vec!["urn:e".into()], ..Default::default() };
        let (assertions, pairs) = range_extension(text, &probes, &hierarchy);
        let ns = "http://km.invalid/ranges#";
        assert!(assertions.contains(&format!("ObjectPropertyAssertion(<urn:r> <{ns}a0> <{ns}b0>)")), "{assertions}");
        assert!(assertions.contains(&format!("ObjectPropertyAssertion(<urn:s> <{ns}a1> <{ns}b1>)")), "{assertions}");
        assert!(!assertions.contains("<urn:e>"), "{assertions}");
        assert_eq!(pairs.len(), 2);
        let types = [
            row(&format!("{ns}b0"), "C"),
            row(&format!("{ns}b0"), OWL_THING),
            row(&format!("{ns}b1"), "D"),
            row("urn:other", "E"),
        ];
        assert_eq!(ranges_from_types(&probes, &pairs, &types), [row("urn:r", "C"), row("urn:s", "D")]);
    }

    #[test]
    fn inconsistent_classification_has_no_property_rows() {
        let _test_env = crate::test_env::write();
        let ns = "http://km.invalid/properties#";
        let mut extended = Classification {
            approximate: None,
            consistent: false,
            subsumptions: vec![],
            unsatisfiable: vec![format!("{ns}some0"), format!("{ns}filler")],
            dropped: 0,
        };
        let hierarchy = split(&mut extended, &probes(), &|_| false).unwrap();
        assert_eq!(hierarchy, PropertyHierarchy::default());
        assert!(extended.unsatisfiable.is_empty());
    }

    #[test]
    fn disagreeing_emptiness_probes_are_refused() {
        let _test_env = crate::test_env::write();
        let ns = "http://km.invalid/properties#";
        let mut extended = Classification {
            approximate: None,
            consistent: true,
            subsumptions: vec![],
            unsatisfiable: vec![format!("{ns}some0")],
            dropped: 0,
        };
        assert!(split(&mut extended, &probes(), &|_| false).is_err());
    }
}
