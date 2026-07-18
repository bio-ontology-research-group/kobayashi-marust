//! Regression witnesses for ORE source IRIs whose final fragment is an OWL
//! builtin spelling. These are ordinary named classes: only the OWL namespace
//! IRIs themselves denote `owl:Thing` and `owl:Nothing`.

use std::collections::{BTreeMap, BTreeSet};

use kobayashi_marust::frontend::{ofn_to_clauses, FrontendResult};
use kobayashi_marust::json_io::JAtom;
use kobayashi_marust::reasoner::Reasoner;

const NESTED_THING: &str =
    "http://purl.obolibrary.org/obo/BFO_0000050_some_http://www.w3.org/2002/07/owl#Thing";
const DAML_NOTHING: &str = "http://www.daml.org/2001/03/daml+oil#Nothing";
const OWL_THING: &str = "http://www.w3.org/2002/07/owl#Thing";

fn frontend(source: &str) -> FrontendResult {
    ofn_to_clauses(source).expect("minimal Functional Syntax ontology must parse")
}

fn internal_name<'a>(result: &'a FrontendResult, full_iri: &str) -> &'a str {
    result
        .iri_map
        .iter()
        .find_map(|(internal, full)| (full == full_iri).then_some(internal.as_str()))
        .unwrap_or_else(|| panic!("missing IRI mapping for {full_iri}"))
}

fn is_concept(atom: &JAtom, expected: &str) -> bool {
    matches!(atom, JAtom::Concept { concept, .. } if concept == expected)
}

fn has_direct_implication(result: &FrontendResult, sub: &str, sup: &str) -> bool {
    result.clauses.iter().any(|clause| {
        clause.body.len() == 1
            && clause.head.len() == 1
            && is_concept(&clause.body[0], sub)
            && is_concept(&clause.head[0], sup)
    })
}

fn classify(result: &FrontendResult) -> BTreeMap<String, BTreeSet<String>> {
    let mut reasoner = Reasoner::new(&result.clauses);
    reasoner.saturate();
    assert!(
        !reasoner.incomplete(),
        "tiny regression ontology must reach a complete fixpoint"
    );
    reasoner.subsumptions()
}

#[test]
fn ore_special_source_iris_remain_named_and_queryable() {
    // ORE 3524 / 15703: this exact told superclass was shortened to bare
    // `Thing`, parsed as top, and lost from 123,310 strict pairs.
    let told = frontend(&format!(
        r#"Ontology(
            Declaration(Class(<http://phenoscape.org/not_has_part/http://purl.obolibrary.org/obo/BFO_0000001>))
            Declaration(Class(<{NESTED_THING}>))
            SubClassOf(
                <http://phenoscape.org/not_has_part/http://purl.obolibrary.org/obo/BFO_0000001>
                <{NESTED_THING}>)
        )"#
    ));
    let child = internal_name(
        &told,
        "http://phenoscape.org/not_has_part/http://purl.obolibrary.org/obo/BFO_0000001",
    );
    let nested_thing = internal_name(&told, NESTED_THING);
    assert!(told.named.iter().any(|name| name == nested_thing));
    assert!(told.declared.iter().any(|name| name == nested_thing));
    assert!(
        has_direct_implication(&told, child, nested_thing),
        "the told subclass axiom must survive clausification"
    );
    let told_taxonomy = classify(&told);
    assert!(
        told_taxonomy
            .get(child)
            .is_some_and(|supers| supers.contains(nested_thing)),
        "the told superclass must survive classification"
    );

    // ORE 13503: this is a legal DAML class, not owl:Nothing. Its stated
    // equivalence to the complement of top makes the named class unsatisfiable.
    let daml = frontend(&format!(
        r#"Ontology(
            Declaration(Class(<{DAML_NOTHING}>))
            EquivalentClasses(
                <{DAML_NOTHING}>
                ObjectComplementOf(owl:Thing))
        )"#
    ));
    let daml_nothing = internal_name(&daml, DAML_NOTHING);
    assert!(daml.named.iter().any(|name| name == daml_nothing));
    assert!(daml.declared.iter().any(|name| name == daml_nothing));
    let daml_taxonomy = classify(&daml);
    assert!(
        daml_taxonomy
            .get(daml_nothing)
            .is_some_and(|supers| supers.contains("owl:Nothing")),
        "the legal DAML class must be emitted as a named unsatisfiable class"
    );

    // ORE 7581 was already full-IRI exact. Keep a witness in which the nested
    // source class coexists with the real OWL top and has a two-way signal.
    let audit = frontend(&format!(
        r#"Ontology(
            Declaration(Class(<{NESTED_THING}>))
            Declaration(Class(<http://example.org/ore-7581#Anchor>))
            EquivalentClasses(
                <{NESTED_THING}>
                <http://example.org/ore-7581#Anchor>)
            SubClassOf(
                <http://example.org/ore-7581#Anchor>
                <{OWL_THING}>)
        )"#
    ));
    let nested_thing = internal_name(&audit, NESTED_THING);
    let anchor = internal_name(&audit, "http://example.org/ore-7581#Anchor");
    assert!(
        !audit.iri_map.values().any(|full| full == OWL_THING),
        "actual OWL top must remain a builtin, not a named source class"
    );
    assert!(has_direct_implication(&audit, nested_thing, anchor));
    assert!(has_direct_implication(&audit, anchor, nested_thing));
    let audit_taxonomy = classify(&audit);
    assert!(audit_taxonomy
        .get(nested_thing)
        .is_some_and(|supers| supers.contains(anchor)));
    assert!(audit_taxonomy
        .get(anchor)
        .is_some_and(|supers| supers.contains(nested_thing)));
}
