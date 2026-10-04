use std::process::Command;

// Independent HermiT-confirmed entailment. Consistency alone is insufficient.
#[test]
fn finite_data_rule_entailments_reach_nominal_class_queries() {
    let input = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/nominal_data_rule_query.ofn");
    let result = Command::new(env!("CARGO_BIN_EXE_km"))
        .env("KM_FINITE_DATA_RULE_NORMALIZE", "1")
        .env("KM_RULE_JOIN_ORDER", "1")
        .env("KM_RULE_ASSERTION_CLOSURE", "1")
        .args(["classify", "--route", "auto"]).arg(input).output().unwrap();
    assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
    let output: serde_json::Value = serde_json::from_slice(&result.stdout).unwrap();
    assert_eq!(output["consistent"], true);
    assert_eq!(output["dropped"], 0);
    assert!(output["subsumptions"].as_array().unwrap().iter().any(|pair|
        pair == &serde_json::json!(["http://km.test/C", "http://km.test/Bad"])),
        "rule consequences must participate in class queries: {output}");
}

#[test]
fn finite_rule_nominal_query_uses_inverse_chain_and_transitive_premises() {
    let source = include_str!("fixtures/nominal_data_rule_query.ofn").replace(
        "ObjectPropertyAssertion(<http://km.test/linked> <http://km.test/a> <http://km.test/b>)",
        r#"Declaration(ObjectProperty(<http://km.test/r>)) Declaration(ObjectProperty(<http://km.test/s>))
        ObjectPropertyAssertion(<http://km.test/r> <http://km.test/m> <http://km.test/a>)
        ObjectPropertyAssertion(<http://km.test/s> <http://km.test/m> <http://km.test/c>)
        ObjectPropertyAssertion(<http://km.test/linked> <http://km.test/c> <http://km.test/b>)
        SubObjectPropertyOf(ObjectPropertyChain(ObjectInverseOf(<http://km.test/r>) <http://km.test/s>) <http://km.test/linked>)
        TransitiveObjectProperty(<http://km.test/linked>)"#,
    );
    let unique = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let input = std::env::temp_dir().join(format!("km-rule-chain-query-{}-{unique}.ofn", std::process::id()));
    std::fs::write(&input, source).unwrap();
    let result = Command::new(env!("CARGO_BIN_EXE_km"))
        .env("KM_FINITE_DATA_RULE_NORMALIZE", "1")
        .env("KM_RULE_JOIN_ORDER", "1")
        .env("KM_RULE_ASSERTION_CLOSURE", "1")
        .args(["classify", "--route", "auto"]).arg(&input).output().unwrap();
    std::fs::remove_file(input).unwrap();
    assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
    let output: serde_json::Value = serde_json::from_slice(&result.stdout).unwrap();
    assert_eq!(output["consistent"], true);
    assert!(output["subsumptions"].as_array().unwrap().iter().any(|pair|
        pair == &serde_json::json!(["http://km.test/C", "http://km.test/Bad"])), "{output}");
    // Noncentral chain clauses remain a separate CB completeness obligation.
    // Do not erase their dropped counter just because this consequence passes.
}

#[test]
fn finite_numeric_rules_keep_named_object_joins_and_nonfunctional_values() {
    let unique = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let directory = std::env::temp_dir().join(format!("km-finite-rules-{}-{unique}", std::process::id()));
    std::fs::create_dir(&directory).unwrap();
    let rule = r#"DLSafeRule(Body(ClassAtom(<http://km.test/P> Variable(<http://km.test/x>)) ClassAtom(<http://km.test/P> Variable(<http://km.test/y>)) ClassAtom(<http://km.test/P> Variable(<http://km.test/z>)) ObjectPropertyAtom(<http://km.test/linked> Variable(<http://km.test/x>) Variable(<http://km.test/y>)) DataPropertyAtom(<http://km.test/value> Variable(<http://km.test/x>) Variable(<http://km.test/aValue>)) DataPropertyAtom(<http://km.test/value> Variable(<http://km.test/y>) Variable(<http://km.test/bValue>)) BuiltInAtom(<http://www.w3.org/2003/11/swrlb#greaterThan> Variable(<http://km.test/d>) "0"^^xsd:int) BuiltInAtom(<http://www.w3.org/2003/11/swrlb#subtract> Variable(<http://km.test/d>) Variable(<http://km.test/bValue>) Variable(<http://km.test/aValue>))) Head(ClassAtom(<http://km.test/Bad> Variable(<http://km.test/y>))))"#;
    for (name, later, edge, extra, consistent) in [
        ("increases", Some("2"), true, "", false),
        ("decreases", Some("0"), true, "", true),
        ("missing", None, true, "", true),
        ("disconnected", Some("2"), false, "", true),
        ("nonfunctional", Some("0"), true, r#"DataPropertyAssertion(<http://km.test/value> <http://km.test/b> "2"^^xsd:float)"#, false),
    ] {
        let input = directory.join(format!("{name}.ofn"));
        let edge = if edge { "ObjectPropertyAssertion(<http://km.test/linked> <http://km.test/a> <http://km.test/b>)" } else { "" };
        let later = later.map(|value| format!("DataPropertyAssertion(<http://km.test/value> <http://km.test/b> \"{value}\"^^xsd:float)")).unwrap_or_default();
        std::fs::write(&input, format!(r#"Ontology(Declaration(Class(<http://km.test/P>)) ClassAssertion(<http://km.test/P> <http://km.test/a>) ClassAssertion(<http://km.test/P> <http://km.test/b>) Declaration(Class(<http://km.test/Bad>)) Declaration(ObjectProperty(<http://km.test/linked>)) Declaration(DataProperty(<http://km.test/value>)) ClassAssertion(ObjectComplementOf(<http://km.test/Bad>) <http://km.test/b>) DataPropertyAssertion(<http://km.test/value> <http://km.test/a> "1"^^xsd:float) {edge} {later} {extra} {rule})"#)).unwrap();
        let result = Command::new(env!("CARGO_BIN_EXE_km"))
            .env("KM_FINITE_DATA_RULE_NORMALIZE", "1")
            .env("KM_RULE_JOIN_ORDER", "1")
            .args(["classify", "--route", "auto"]).arg(input).output().unwrap();
        assert!(result.status.success(), "{name}: {}", String::from_utf8_lossy(&result.stderr));
        let output: serde_json::Value = serde_json::from_slice(&result.stdout).unwrap();
        assert_eq!(output["consistent"], consistent, "{name}: {output}");
        assert_eq!(output["dropped"], 0, "{name}: {output}");
    }
    std::fs::remove_dir_all(directory).unwrap();
}
