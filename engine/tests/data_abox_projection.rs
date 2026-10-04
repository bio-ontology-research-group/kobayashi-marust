use std::process::Command;

#[test]
fn independent_data_abox_preserves_domains_values_and_future_equalities() {
    for automatic in [false, true] {
    for (label, first, second, extra, consistent) in [
        ("distinct-owners", "1", "2", "", true),
        ("merged-owners", "1", "2", "SameIndividual(<urn:a> <urn:b>)", false),
        ("equal-values", "1", "01", "SameIndividual(<urn:a> <urn:b>)", true),
        ("domain-clash", "1", "2", "ClassAssertion(<urn:Bad> <urn:a>)", false),
        ("range-clash", "1", "3", "", false),
    ] {
        let source = format!(r#"Ontology(
            Declaration(Class(<urn:C>)) Declaration(Class(<urn:Bad>))
            Declaration(Class(<urn:Universal>)) Declaration(ObjectProperty(<urn:r>))
            InverseFunctionalObjectProperty(<urn:r>)
            Declaration(DataProperty(<urn:p>)) Declaration(DataProperty(<urn:q>))
            Declaration(NamedIndividual(<urn:a>)) Declaration(NamedIndividual(<urn:b>))
            EquivalentClasses(<urn:Universal> ObjectAllValuesFrom(<urn:r> <urn:C>))
            DisjointClasses(<urn:C> <urn:Bad>)
            SubDataPropertyOf(<urn:p> <urn:q>) FunctionalDataProperty(<urn:q>)
            DataPropertyDomain(<urn:q> <urn:C>)
            DataPropertyRange(<urn:q> DataOneOf("1"^^xsd:int "2"^^xsd:int))
            DataPropertyAssertion(<urn:p> <urn:a> "{first}"^^xsd:integer)
            DataPropertyAssertion(<urn:p> <urn:b> "{second}"^^xsd:int)
            {extra})"#);
        let path = std::env::temp_dir().join(format!("km-data-projection-{}-{label}.ofn", std::process::id()));
        std::fs::write(&path, &source).unwrap();
        let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
        command.env_remove("KM_GROUND_RULE_SOURCE").env("KM_TIMING", "1");
        if automatic { command.env_remove("KM_DATA_ABOX_PROJECT"); }
        else { command.env("KM_DATA_ABOX_PROJECT", "1"); }
        let output = command.args(["classify", "--route", if automatic { "auto" } else { "ht_bridge" }])
            .arg(&path).output().unwrap();
        if automatic {
            assert!(String::from_utf8_lossy(&output.stderr).contains("automatic data source accepted: KM_DATA_ABOX_PROJECT"),
                "{label}: {}", String::from_utf8_lossy(&output.stderr));
        }
        assert_eq!(std::fs::read_to_string(&path).unwrap(), source);
        std::fs::remove_file(&path).unwrap();
        assert!(output.status.success(), "{label}: {}", String::from_utf8_lossy(&output.stderr));
        let result: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(result["consistent"], consistent, "{label}: {result}");
        assert_eq!(result["dropped"], 0, "{label}: {result}");
    }
}

}

#[test]
fn automatic_native_attempt_preserves_same_and_vacuous_rule_semantics() {
    for (name, source, consistent) in [
        ("same-finite", r#"Ontology(
            Declaration(Class(<urn:C>)) Declaration(Class(<urn:D>))
            Declaration(DataProperty(<urn:p>))
            DataPropertyRange(<urn:p> DataOneOf("red"^^xsd:string "blue"^^xsd:string))
            ClassAssertion(<urn:C> <urn:a>) ClassAssertion(<urn:D> <urn:b>)
            DisjointClasses(<urn:C> <urn:D>) SameIndividual(<urn:a> <urn:b>))"#, false),
        ("empty-rule-domain", r#"Ontology(
            Declaration(ObjectProperty(<urn:r>)) Declaration(ObjectProperty(<urn:s>))
            Declaration(Class(<urn:C>)) Declaration(Class(<urn:D>))
            Declaration(DataProperty(<urn:p>))
            DataPropertyRange(<urn:p> xsd:string)
            DLSafeRule(Body(ClassAtom(<urn:C> Variable(<urn:x>)))
                Head(DataPropertyAtom(<urn:p> Variable(<urn:x>) "red"^^xsd:string)))
            SubObjectPropertyOf(ObjectPropertyChain(<urn:r> <urn:r>) <urn:s>)
            DLSafeRule(Body(ClassAtom(<urn:C> Variable(<urn:x>)))
                Head(ClassAtom(<urn:D> Variable(<urn:x>)))))"#, true),
    ] {
        let path = std::env::temp_dir().join(format!("km-native-source-{}-{name}.ofn", std::process::id()));
        std::fs::write(&path, source).unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_km"))
            .env_remove("KM_DATA_ABOX_PROJECT").env_remove("KM_GROUND_RULE_SOURCE")
            .env("KM_TIMING", "1").args(["classify", "--route", "auto"]).arg(&path).output().unwrap();
        assert_eq!(std::fs::read_to_string(&path).unwrap(), source);
        std::fs::remove_file(path).unwrap();
        assert!(output.status.success(), "{name}: {}", String::from_utf8_lossy(&output.stderr));
        assert!(String::from_utf8_lossy(&output.stderr).contains("automatic data source accepted: native"),
            "{name}: {}", String::from_utf8_lossy(&output.stderr));
        let result: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(result["consistent"], consistent, "{name}: {result}");
        assert_eq!(result["dropped"], 0);
        if consistent {
            assert!(!result["subsumptions"].as_array().unwrap().contains(&serde_json::json!(["urn:C", "urn:D"])),
                "DL-safe rule over no named individuals must not become a universal class inclusion");
        }
    }
}
