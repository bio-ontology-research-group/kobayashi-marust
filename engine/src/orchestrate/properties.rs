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
//! `P_e ≡ ∃e.B`, plus `P_⊤ ≡ ∃owl:topObjectProperty.B`, and for each named `r`
//! the fresh classes `Dom_r ≡ ∃r.⊤` and `Ran_r ≡ ∃r⁻.⊤`. The extension only
//! defines fresh names, so it is conservative. Because `B` is fresh it can be
//! interpreted as any set, in particular a singleton `{y}`:
//!
//! * if `(x, y) ∈ e \ f` in a model of `O`, set `B = {y}`: then
//!   `x ∈ P_e \ P_f`; conversely `x ∈ P_e \ P_f` gives a `y ∈ B` with
//!   `(x, y) ∈ e \ f`. So `O ⊨ e ⊑ f` iff `O' ⊨ P_e ⊑ P_f`;
//! * `e` is empty iff `P_e` is unsatisfiable;
//! * `owl:topObjectProperty ⊑ f` iff `P_⊤ ⊑ P_f`.
//!
//! One classification of `O'` answers all of it; rows that mention a probe
//! class are removed from the taxonomy, which leaves the classification of `O`.

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
    /// `∃r.⊤` for the named property with this index.
    Domain(usize),
    /// `∃r⁻.⊤` for the named property with this index.
    Range(usize),
}

/// The probe classes of one extension.
#[derive(Clone, Debug)]
pub struct PropertyProbes {
    /// Probe IRI (as the output spells it) to what it stands for.
    probes: BTreeMap<String, Probe>,
    /// Public names: `2 i` is the named property `i`, `2 i + 1` its inverse.
    expressions: Vec<String>,
}

impl PropertyProbes {
    fn named(&self, index: usize) -> &str {
        &self.expressions[2 * index]
    }

    /// Is `name` one of these probe classes?
    pub(super) fn is_probe(&self, name: &str) -> bool {
        self.probes.contains_key(name)
    }
}

/// The probe axioms for `properties` (source spellings) and their probes.
pub(super) fn extension(text: &str, properties: &[String]) -> (String, PropertyProbes) {
    let ns = fresh_namespace_for(text, "properties");
    let mut out = String::with_capacity(properties.len() * 512 + 256);
    let mut probes = BTreeMap::new();
    let mut expressions = Vec::with_capacity(properties.len() * 2);
    let filler = format!("{ns}filler");
    let top = format!("{ns}top");
    out.push_str(&format!("Declaration(Class(<{filler}>))\nDeclaration(Class(<{top}>))\n"));
    out.push_str(&format!(
        "EquivalentClasses(<{top}> ObjectSomeValuesFrom(owl:topObjectProperty <{filler}>))\n"
    ));
    probes.insert(filler.clone(), Probe::Filler);
    probes.insert(top, Probe::Top);
    for (index, token) in properties.iter().enumerate() {
        let name = public_name(token);
        expressions.push(name.clone());
        expressions.push(format!("ObjectInverseOf({name})"));
        let inverse = format!("ObjectInverseOf({token})");
        for (offset, expression) in [token.as_str(), inverse.as_str()].into_iter().enumerate() {
            let probe = format!("{ns}some{}", 2 * index + offset);
            out.push_str(&format!(
                "Declaration(Class(<{probe}>))\nEquivalentClasses(<{probe}> ObjectSomeValuesFrom({expression} <{filler}>))\n"
            ));
            probes.insert(probe, Probe::Some(2 * index + offset));
        }
        let domain = format!("{ns}domain{index}");
        let range = format!("{ns}range{index}");
        out.push_str(&format!(
            "Declaration(Class(<{domain}>))\nEquivalentClasses(<{domain}> ObjectSomeValuesFrom({token} owl:Thing))\n\
             Declaration(Class(<{range}>))\nEquivalentClasses(<{range}> ObjectSomeValuesFrom({inverse} owl:Thing))\n"
        ));
        probes.insert(domain, Probe::Domain(index));
        probes.insert(range, Probe::Range(index));
    }
    (out, PropertyProbes { probes, expressions })
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
            (Some(Probe::Domain(r)), None) if high != OWL_THING && !foreign(&high) => {
                domains.insert([probes.named(r).to_string(), high]);
            }
            (Some(Probe::Range(r)), None) if high != OWL_THING && !foreign(&high) => {
                ranges.insert([probes.named(r).to_string(), high]);
            }
            // Mirrors of reported pairs, `∃e.B ⊑ C` (the domain again), and
            // facts about source classes or individual probes.
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
        let empty = [Probe::Some(2 * index), Probe::Some(2 * index + 1), Probe::Domain(index), Probe::Range(index)]
            .map(|p| unsatisfiable.contains(&p));
        if empty.iter().any(|&e| e) != empty.iter().all(|&e| e) {
            // `r`, `r⁻`, `∃r.⊤` and `∃r⁻.⊤` are empty together in every model.
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

    #[test]
    fn extension_defines_every_probe() {
        let text = "Ontology(<urn:o> SubObjectPropertyOf(<urn:r> <urn:s>))";
        let roles = source_object_properties(text).unwrap();
        let (extension, probes) = extension(text, &roles);
        assert_eq!(probes.expressions, ["urn:r", "ObjectInverseOf(urn:r)", "urn:s", "ObjectInverseOf(urn:s)"]);
        let ns = "http://km.invalid/properties#";
        for line in [
            format!("EquivalentClasses(<{ns}top> ObjectSomeValuesFrom(owl:topObjectProperty <{ns}filler>))"),
            format!("EquivalentClasses(<{ns}some0> ObjectSomeValuesFrom(<urn:r> <{ns}filler>))"),
            format!("EquivalentClasses(<{ns}some1> ObjectSomeValuesFrom(ObjectInverseOf(<urn:r>) <{ns}filler>))"),
            format!("EquivalentClasses(<{ns}domain1> ObjectSomeValuesFrom(<urn:s> owl:Thing))"),
            format!("EquivalentClasses(<{ns}range1> ObjectSomeValuesFrom(ObjectInverseOf(<urn:s>) owl:Thing))"),
        ] {
            assert!(extension.contains(&line), "{line}");
        }
        assert_eq!(probes.probes.len(), 2 + 4 * 2);
    }

    fn row(a: &str, b: &str) -> [String; 2] {
        [a.to_string(), b.to_string()]
    }

    fn probes() -> PropertyProbes {
        let text = "Ontology(<urn:o> SubObjectPropertyOf(<urn:r> <urn:s>) ObjectPropertyDomain(<urn:e> owl:Nothing))";
        let roles = source_object_properties(text).unwrap();
        extension(text, &roles).1
    }

    #[test]
    fn split_reads_property_rows_and_keeps_source_rows() {
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
                row(&p("domain0"), "A"),
                row(&p("domain0"), OWL_THING),
                row(&p("range0"), "B"),
                row(&p("domain2"), "T"),
                row("A", &p("some0")),
            ],
            unsatisfiable: vec!["U".into(), p("some4"), p("some5"), p("domain2"), p("range2")],
            dropped: 0,
        };
        let hierarchy = split(&mut extended, &probes(), &|_| false).unwrap();
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
    fn inconsistent_classification_has_no_property_rows() {
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
