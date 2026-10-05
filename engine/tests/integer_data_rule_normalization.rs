use std::process::Command;

#[test]
fn integer_rule_threshold_is_enforced_only_on_the_dl_safe_domain() {
    let unique = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let directory = std::env::temp_dir().join(format!("km-integer-rule-{}-{unique}", std::process::id()));
    std::fs::create_dir(&directory).unwrap();
    let rule = r#"DLSafeRule(Body(ClassAtom(:Person Variable(:p)) DataPropertyAtom(:age Variable(:p) Variable(:v)) BuiltInAtom(<http://www.w3.org/2003/11/swrlb#greaterThan> Variable(:v) "17"^^xsd:integer)) Head(ClassAtom(:Adult Variable(:p))))"#;
    for (name, assertions, consistent) in [
        ("adult", r#"ClassAssertion(:Person :i) ClassAssertion(ObjectComplementOf(:Adult) :i) DataPropertyAssertion(:age :i "18"^^xsd:int)"#, false),
        ("subproperty", r#"Declaration(DataProperty(:otherAge)) SubDataPropertyOf(:otherAge :age) ClassAssertion(:Person :i) ClassAssertion(ObjectComplementOf(:Adult) :i) DataPropertyAssertion(:otherAge :i "18"^^xsd:int)"#, false),
        ("float_signed_zero", r#"Declaration(DataProperty(:dose)) FunctionalDataProperty(:dose) DataPropertyAssertion(:dose :j "+0"^^xsd:float) DataPropertyAssertion(:dose :j "-0"^^xsd:float)"#, false),
        ("datetime_offsets", r#"Declaration(DataProperty(:birth)) FunctionalDataProperty(:birth) DataPropertyAssertion(:birth :j "1956-06-25T04:00:00-05:00"^^xsd:dateTime) DataPropertyAssertion(:birth :j "1956-06-25T10:00:00+01:00"^^xsd:dateTime)"#, false),
        ("minor", r#"ClassAssertion(:Person :i) ClassAssertion(ObjectComplementOf(:Adult) :i) DataPropertyAssertion(:age :i "17"^^xsd:int)"#, true),
        ("anonymous", r#"Declaration(NamedIndividual(:unrelated)) SubClassOf(:Person DataHasValue(:age "18"^^xsd:int)) SubClassOf(:Person ObjectComplementOf(:Adult))"#, true),
    ] {
        let input = directory.join(format!("{name}.ofn"));
        std::fs::write(&input, format!("Prefix(:=<http://km.test/>) Ontology(Declaration(Class(:Person)) Declaration(Class(:Adult)) Declaration(DataProperty(:age)) DataPropertyRange(:age xsd:int) {assertions} {rule})")).unwrap();
        let result = Command::new(env!("CARGO_BIN_EXE_km"))
            .env_remove("KM_UNARY_DATA_RULE_NORMALIZE")
            .env_remove("KM_NO_UNARY_DATA_RULE_NORMALIZE")
            .args(["classify", "--route", "auto"]).arg(input).output().unwrap();
        assert!(result.status.success(), "{name}: {}", String::from_utf8_lossy(&result.stderr));
        let output: serde_json::Value = serde_json::from_slice(&result.stdout).unwrap();
        assert_eq!(output["consistent"], consistent, "{name}");
        assert_eq!(output["dropped"], 0, "{name}");
        if name == "adult" {
            let disabled = Command::new(env!("CARGO_BIN_EXE_km"))
                .env("KM_NO_UNARY_DATA_RULE_NORMALIZE", "1")
                .env_remove("KM_UNARY_DATA_RULE_NORMALIZE")
                .env_remove("KM_CONSTANT_DATA_RULE_NORMALIZE")
                .args(["classify", "--route", "auto"]).arg(directory.join("adult.ofn"))
                .output().unwrap();
            assert!(!disabled.status.success(), "disabled normalization must retain the concrete obligation");
        }
        if name == "anonymous" {
            assert!(!output["unsatisfiable"].as_array().unwrap().contains(&serde_json::json!("http://km.test/Person")));
        }
    }
    std::fs::remove_dir_all(directory).unwrap();
}

#[test]
fn self_role_rule_preserves_constant_data_heads_and_named_guard() {
    let unique = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let directory = std::env::temp_dir().join(format!("km-self-data-rule-{}-{unique}", std::process::id()));
    std::fs::create_dir(&directory).unwrap();
    let rule = r#"DLSafeRule(Body(ObjectPropertyAtom(:followedBy Variable(:x) Variable(:x))) Head(DataPropertyAtom(:hasError Variable(:x) "list error")))"#;
    for (name, assertions, consistent) in [
        ("self", r#"ObjectPropertyAssertion(:followedBy :i :i) ClassAssertion(DataAllValuesFrom(:hasError DataComplementOf(DataOneOf("list error"))) :i)"#, false),
        ("other", r#"ObjectPropertyAssertion(:followedBy :i :j) ClassAssertion(DataAllValuesFrom(:hasError DataComplementOf(DataOneOf("list error"))) :i)"#, true),
        ("anonymous", r#"Declaration(NamedIndividual(:unrelated)) SubClassOf(:Item ObjectHasSelf(:followedBy)) SubClassOf(:Item DataAllValuesFrom(:hasError DataComplementOf(DataOneOf("list error"))))"#, true),
    ] {
        let input = directory.join(format!("{name}.ofn"));
        std::fs::write(&input, format!("Prefix(:=<http://km.test/>) Ontology(Declaration(Class(:Item)) Declaration(ObjectProperty(:followedBy)) Declaration(DataProperty(:hasError)) {assertions} {rule})")).unwrap();
        let result = Command::new(env!("CARGO_BIN_EXE_km"))
            .env_remove("KM_UNARY_DATA_RULE_NORMALIZE")
            .env_remove("KM_NO_UNARY_DATA_RULE_NORMALIZE")
            .args(["classify", "--route", "auto"]).arg(input).output().unwrap();
        assert!(result.status.success(), "{name}: {}", String::from_utf8_lossy(&result.stderr));
        let output: serde_json::Value = serde_json::from_slice(&result.stdout).unwrap();
        assert_eq!(output["consistent"], consistent, "{name}");
        assert_eq!(output["dropped"], 0, "{name}");
        if name == "anonymous" {
            assert!(!output["unsatisfiable"].as_array().unwrap().contains(&serde_json::json!("http://km.test/Item")));
        }
    }
    std::fs::remove_dir_all(directory).unwrap();
}
