//! Regression for parent class labels consumed across an inverse role edge.
use std::process::Command;

fn classify(case: &str, axioms: &str) -> serde_json::Value {
    let path = std::env::temp_dir().join(format!("km-inverse-parent-{}-{case}.ofn", std::process::id()));
    std::fs::write(&path, axioms).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_km"))
        .args(["classify", "--route", "cb_plain1"])
        .env_remove("KM_RSUCC")
        .arg(&path).output().unwrap();
    std::fs::remove_file(path).unwrap();
    assert!(output.status.success(), "{case}: {}", String::from_utf8_lossy(&output.stderr));
    let answer: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(answer["consistent"], true, "{case}");
    assert_eq!(answer["dropped"], 0, "{case}");
    answer
}

fn entails(answer: &serde_json::Value, sub: &str, sup: &str) -> bool {
    let mut reached = std::collections::BTreeSet::from([sub]);
    loop {
        let before = reached.len();
        for edge in answer["subsumptions"].as_array().unwrap() {
            let a = edge[0].as_str().unwrap();
            let b = edge[1].as_str().unwrap();
            if reached.contains(a) { reached.insert(b); }
        }
        if reached.len() == before { return reached.contains(sup); }
    }
}

#[test]
fn inverse_parent_labels_preserve_disjunctions_and_shared_successor_conditions() {
    for (name, extra, expected) in [
        ("positive", "SubClassOf(<urn:probe:A> <urn:probe:P>)", true),
        ("unresolved", "SubClassOf(<urn:probe:A> ObjectUnionOf(<urn:probe:P> <urn:probe:S>))", false),
        ("both", "SubClassOf(<urn:probe:A> ObjectUnionOf(<urn:probe:P> <urn:probe:S>))\nSubClassOf(ObjectSomeValuesFrom(<urn:probe:ri> <urn:probe:S>) <urn:probe:Q>)", true),
    ] {
        let input = format!("Ontology(
            Declaration(Class(<urn:probe:A>)) Declaration(Class(<urn:probe:B>))
            Declaration(Class(<urn:probe:C>)) Declaration(Class(<urn:probe:D>))
            Declaration(Class(<urn:probe:P>)) Declaration(Class(<urn:probe:Q>))
            Declaration(Class(<urn:probe:S>))
            Declaration(ObjectProperty(<urn:probe:r>)) Declaration(ObjectProperty(<urn:probe:ri>))
            InverseObjectProperties(<urn:probe:r> <urn:probe:ri>)
            SubClassOf(<urn:probe:A> ObjectSomeValuesFrom(<urn:probe:r> <urn:probe:C>))
            SubClassOf(<urn:probe:B> ObjectSomeValuesFrom(<urn:probe:r> <urn:probe:C>))
            SubClassOf(ObjectSomeValuesFrom(<urn:probe:ri> <urn:probe:P>) <urn:probe:Q>)
            SubClassOf(ObjectSomeValuesFrom(<urn:probe:r> <urn:probe:Q>) <urn:probe:D>)
            {extra})");
        let answer = classify(name, &input);
        assert_eq!(entails(&answer, "urn:probe:A", "urn:probe:D"), expected, "{name}");
        assert!(!entails(&answer, "urn:probe:B", "urn:probe:D"), "{name}: shared successor leaked a conditional label");
    }
}

#[test]
fn inverse_transitivity_chain_reconstructs_the_9684_consequence() {
    let answer = classify("transitivity", include_str!("fixtures/inverse_predecessor_transitivity.ofn"));
    assert!(entails(&answer,
        "http://purl.org/obo/owl/UBERON#UBERON_0004277",
        "http://purl.org/obo/owl/UBERON#UBERON_0004121"));
}
