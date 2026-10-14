//! Native bridge regressions from the Wine 1-DPA family (ORE 11477, 13954,
//! 1397, 14334, 3010, 8786).
//!
//! 1. Data successors share the completion graph with objects. The bridge
//!    admitted a datatype ontology only when an isolated element with the EMPTY
//!    label satisfies every object axiom; `NonConsumable == not(Consumable)`
//!    fails that. Admission now also accepts a non-empty isolated witness label
//!    (`LabelledIsolatedExtension` in Lean): the represented theory is
//!    equisatisfiable, so verdicts are unchanged. Without a witness it still
//!    defers.
//! 2. Backend-reuse same-individual merging resolved both representative ids
//!    of an earlier `SameIndividual` merge to ONE node and merged that node into
//!    itself, pruning it. A new predecessor of the nominal then never received
//!    its `forall hasColor-` trigger and the bridge missed a subsumption.
use std::process::Command;

fn run(source: &str, tag: &str) -> std::process::Output {
    let dir = std::env::temp_dir().join(format!("km-bridge-wine-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("{tag}.ofn"));
    std::fs::write(&path, source).unwrap();
    Command::new(env!("CARGO_BIN_EXE_km"))
        .args(["classify", "--route", "ht_bridge"])
        .arg(&path)
        .output()
        .expect("run km classification")
}

fn pairs(output: &std::process::Output) -> Vec<serde_json::Value> {
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    let value: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(value["consistent"], true);
    assert_eq!(value["dropped"], 0);
    value["subsumptions"].as_array().unwrap().clone()
}

const SAME_INDIVIDUAL_REUSE: &str = r#"Ontology(<urn:t>
Declaration(Class(<urn:t#Muscadet>)) Declaration(Class(<urn:t#PinotBlanc>)) Declaration(Class(<urn:t#Wine>)) Declaration(Class(<urn:t#WhiteWine>)) Declaration(Class(<urn:t#WhiteNonSweetWine>))
Declaration(ObjectProperty(<urn:t#hasSugar>)) Declaration(ObjectProperty(<urn:t#madeFromGrape>)) Declaration(ObjectProperty(<urn:t#hasColor>))
Declaration(NamedIndividual(<urn:t#Dry>)) Declaration(NamedIndividual(<urn:t#OffDry>)) Declaration(NamedIndividual(<urn:t#PinotBlancGrape>)) Declaration(NamedIndividual(<urn:t#White>)) Declaration(NamedIndividual(<urn:u#White>))
SubClassOf(<urn:t#Muscadet> ObjectHasValue(<urn:t#hasSugar> <urn:t#Dry>))
SubClassOf(<urn:t#Muscadet> ObjectHasValue(<urn:t#madeFromGrape> <urn:t#PinotBlancGrape>))
SubClassOf(<urn:t#Muscadet> ObjectMaxCardinality(1 <urn:t#madeFromGrape>))
EquivalentClasses(<urn:t#PinotBlanc> ObjectIntersectionOf(<urn:t#Wine> ObjectHasValue(<urn:t#madeFromGrape> <urn:t#PinotBlancGrape>) ObjectMaxCardinality(1 <urn:t#madeFromGrape>)))
SubClassOf(<urn:t#PinotBlanc> ObjectHasValue(<urn:t#hasColor> <urn:t#White>))
EquivalentClasses(<urn:t#WhiteNonSweetWine> ObjectIntersectionOf(ObjectAllValuesFrom(<urn:t#hasSugar> ObjectOneOf(<urn:t#Dry> <urn:t#OffDry>)) <urn:t#WhiteWine>))
EquivalentClasses(<urn:t#WhiteWine> ObjectIntersectionOf(ObjectHasValue(<urn:t#hasColor> <urn:t#White>) <urn:t#Wine>))
FunctionalObjectProperty(<urn:t#hasSugar>)
ObjectPropertyDomain(<urn:t#madeFromGrape> <urn:t#Wine>)
SameIndividual(<urn:u#White> <urn:t#White>)
)
"#;

#[test]
fn same_individual_backend_reuse_keeps_the_merged_nominal_live() {
    let pairs = pairs(&run(SAME_INDIVIDUAL_REUSE, "same-reuse"));
    for expected in [
        ["urn:t#Muscadet", "urn:t#WhiteNonSweetWine"],
        ["urn:t#Muscadet", "urn:t#WhiteWine"],
        ["urn:t#Muscadet", "urn:t#PinotBlanc"],
    ] {
        assert!(pairs.contains(&serde_json::json!(expected)), "missing {expected:?}");
    }
}

fn blank_witness_source(extra: &str) -> String {
    format!(
        r#"Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)
Ontology(<urn:t>
Declaration(Class(<urn:t#Consumable>)) Declaration(Class(<urn:t#NonConsumable>)) Declaration(Class(<urn:t#A>)) Declaration(Class(<urn:t#B>)) Declaration(Class(<urn:t#C>))
Declaration(DataProperty(<urn:t#p>)) Declaration(ObjectProperty(<urn:t#r>)) Declaration(NamedIndividual(<urn:t#a>))
EquivalentClasses(<urn:t#NonConsumable> ObjectComplementOf(<urn:t#Consumable>))
SubClassOf(<urn:t#A> <urn:t#Consumable>)
SubClassOf(<urn:t#A> DataSomeValuesFrom(<urn:t#p> xsd:integer))
SubClassOf(<urn:t#C> ObjectIntersectionOf(<urn:t#A> <urn:t#B>))
DataPropertyDomain(<urn:t#p> <urn:t#A>)
DataPropertyRange(<urn:t#p> xsd:integer)
ClassAssertion(<urn:t#C> <urn:t#a>)
{extra}
)
"#
    )
}

#[test]
fn a_nonempty_isolated_witness_label_admits_the_datatype_bridge() {
    let pairs = pairs(&run(&blank_witness_source(""), "witness"));
    for expected in [
        ["urn:t#A", "urn:t#Consumable"],
        ["urn:t#C", "urn:t#A"],
        ["urn:t#C", "urn:t#B"],
        ["urn:t#C", "urn:t#Consumable"],
    ] {
        assert!(pairs.contains(&serde_json::json!(expected)), "missing {expected:?}");
    }
    assert!(!pairs.contains(&serde_json::json!(["urn:t#A", "urn:t#C"])));
}

#[test]
fn without_an_isolated_witness_label_the_datatype_bridge_still_defers() {
    let output = run(
        &blank_witness_source(
            "SubClassOf(<urn:t#Consumable> ObjectSomeValuesFrom(<urn:t#r> <urn:t#B>))\n\
             SubClassOf(<urn:t#NonConsumable> ObjectSomeValuesFrom(<urn:t#r> <urn:t#B>))",
        ),
        "no-witness",
    );
    assert!(!output.status.success(), "an isolated data node has no model here; the route must defer");
}
