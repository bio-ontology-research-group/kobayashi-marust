use std::process::Command;

#[test]
fn constant_data_rule_conclusions_reach_nominal_class_queries() {
    let input = std::env::temp_dir().join(format!("km-constant-rule-query-{}.ofn", std::process::id()));
    std::fs::write(&input, r#"Prefix(:=<http://km.test/>) Ontology(
      Declaration(Class(<http://km.test/C>)) Declaration(Class(<http://km.test/Bad>))
      Declaration(ObjectProperty(<http://km.test/r>)) Declaration(DataProperty(<http://km.test/p>))
      SubClassOf(<http://km.test/C> ObjectOneOf(<http://km.test/b>))
      ObjectPropertyAssertion(<http://km.test/r> <http://km.test/a> <http://km.test/b>)
      DataPropertyAssertion(<http://km.test/p> <http://km.test/a> "NULL"^^xsd:string)
      DLSafeRule(Body(ObjectPropertyAtom(<http://km.test/r> Variable(<http://km.test/x>) Variable(<http://km.test/y>))
        DataPropertyAtom(<http://km.test/p> Variable(<http://km.test/x>) "NULL"^^xsd:string))
        Head(ClassAtom(<http://km.test/Bad> Variable(<http://km.test/y>)))))"#).unwrap();
    let result = Command::new(env!("CARGO_BIN_EXE_km"))
        .env("KM_CONSTANT_DATA_RULE_NORMALIZE", "1")
        .env_remove("KM_RULE_ASSERTION_CLOSURE")
        .args(["classify", "--route", "auto"]).arg(&input).output().unwrap();
    std::fs::remove_file(input).unwrap();
    assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
    let output: serde_json::Value = serde_json::from_slice(&result.stdout).unwrap();
    assert_eq!(output["consistent"], true);
    assert_eq!(output["dropped"], 0);
    assert!(output["subsumptions"].as_array().unwrap().contains(
        &serde_json::json!(["http://km.test/C", "http://km.test/Bad"])), "{output}");
}

#[test]
fn constant_data_rule_keeps_object_joins_and_named_bindings() {
    let unique = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let directory = std::env::temp_dir().join(format!("km-constant-rule-{}-{unique}", std::process::id()));
    std::fs::create_dir(&directory).unwrap();
    let rule = r#"DLSafeRule(Body(ObjectPropertyAtom(:partOf Variable(:x) Variable(:y)) DataPropertyAtom(:default Variable(:x) "NULL"^^xsd:string)) Head(ClassAtom(:Bad Variable(:y))))"#;
    for (name, facts, consistent) in [
        ("joined", r#"ObjectPropertyAssertion(:partOf :a :b) DataPropertyAssertion(:default :a "NULL"^^xsd:string) ClassAssertion(ObjectComplementOf(:Bad) :b)"#, false),
        ("different", r#"ObjectPropertyAssertion(:partOf :a :b) DataPropertyAssertion(:default :a "other"^^xsd:string) ClassAssertion(ObjectComplementOf(:Bad) :b)"#, true),
        ("disconnected", r#"ObjectPropertyAssertion(:partOf :c :b) DataPropertyAssertion(:default :a "NULL"^^xsd:string) ClassAssertion(ObjectComplementOf(:Bad) :b)"#, true),
        ("anonymous", r#"Declaration(NamedIndividual(:unrelated)) SubClassOf(:Item DataHasValue(:default "NULL"^^xsd:string)) SubClassOf(:Item ObjectSomeValuesFrom(:partOf ObjectComplementOf(:Bad)))"#, true),
        ("collision", r#"Declaration(Class(:__rule_data_const_0)) SubClassOf(:__rule_data_const_0 owl:Nothing) ObjectPropertyAssertion(:partOf :a :b) DataPropertyAssertion(:default :a "NULL"^^xsd:string)"#, true),
    ] {
        let input = directory.join(format!("{name}.ofn"));
        std::fs::write(&input, format!("Prefix(:=<http://km.test/>) Ontology(Declaration(Class(:Item)) Declaration(Class(:Bad)) Declaration(ObjectProperty(:partOf)) Declaration(DataProperty(:default)) {facts} {rule})")).unwrap();
        let result = Command::new(env!("CARGO_BIN_EXE_km"))
            .env_remove("KM_UNARY_DATA_RULE_NORMALIZE")
            .env("KM_CONSTANT_DATA_RULE_NORMALIZE", "1")
            .args(["classify", "--route", "auto"]).arg(input).output().unwrap();
        assert!(result.status.success(), "{name}: {}", String::from_utf8_lossy(&result.stderr));
        let output: serde_json::Value = serde_json::from_slice(&result.stdout).unwrap();
        assert_eq!(output["consistent"], consistent, "{name}: {output}");
        assert_eq!(output["dropped"], 0, "{name}: {output}");
    }
    std::fs::remove_dir_all(directory).unwrap();
}
