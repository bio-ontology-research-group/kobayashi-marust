use std::process::{Command, Output};

const SOURCE: &str = include_str!("fixtures/symbolic_source_cardinality.ofn");

fn classify(source: &str, certificate: bool) -> Output {
    classify_mode(source, certificate, true)
}

fn classify_mode(source: &str, certificate: bool, explicit: bool) -> Output {
    let stamp = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let input = std::env::temp_dir().join(format!("km-symbolic-source-{}-{stamp}.ofn", std::process::id()));
    std::fs::write(&input, source).unwrap();
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    command.env_remove("KM_SYMBOLIC_SOURCE_BRIDGE").env_remove("KM_NO_SYMBOLIC_SOURCE_BRIDGE")
        .env_remove("KM_TRIGGER_ABSORB").env_remove("KM_HT_LEAN_CERT_CHECKER")
        .args(["classify", "--route", "auto"]).arg(&input);
    if explicit { command.env("KM_SYMBOLIC_SOURCE_BRIDGE", "1"); }
    if certificate { command.env("KM_HT_LEAN_CERT_CHECKER", "/missing-symbolic-source-checker"); }
    let result = command.output().unwrap();
    std::fs::remove_file(input).unwrap();
    result
}

#[test]
fn symbolic_qualified_bounds_and_datatypes_publish_full_iris() {
    let result = classify(SOURCE, false);
    assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
    let output: serde_json::Value = serde_json::from_slice(&result.stdout).unwrap();
    assert_eq!(output["consistent"], true);
    assert_eq!(output["dropped"], 0);
    assert_eq!(output["unsatisfiable"], serde_json::json!(["http://x#A"]));
    for pair in output["subsumptions"].as_array().unwrap() {
        for name in pair.as_array().unwrap() {
            assert!(name.as_str().unwrap().starts_with("http://x#"));
        }
    }
}

#[test]
fn symbolic_unsatisfiable_assertion_is_global_inconsistency() {
    let source = SOURCE.replacen("Ontology(", "Ontology(ClassAssertion(<http://x#A> <http://x#a>) ", 1);
    let result = classify(&source, false);
    assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
    let output: serde_json::Value = serde_json::from_slice(&result.stdout).unwrap();
    assert_eq!(output["consistent"], false);
    assert_eq!(output["subsumptions"], serde_json::json!([]));
    assert_eq!(output["unsatisfiable"], serde_json::json!([]));
}

#[test]
fn symbolic_entry_cannot_bypass_requested_runtime_certificate() {
    let result = classify(SOURCE, true);
    assert!(!result.status.success());
    assert!(String::from_utf8_lossy(&result.stderr).contains("cannot bypass requested HT runtime certification"));
}

#[test]
fn symbolic_matching_bounds_with_assertion_remain_consistent() {
    let source = SOURCE.replace("ObjectMaxCardinality(2", "ObjectMaxCardinality(3")
        .replacen("Ontology(", "Ontology(ClassAssertion(<http://x#A> <http://x#a>) ", 1);
    assert_ne!(source, SOURCE);
    let result = classify(&source, false);
    assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
    let output: serde_json::Value = serde_json::from_slice(&result.stdout).unwrap();
    assert_eq!(output["consistent"], true);
    assert_eq!(output["dropped"], 0);
    assert_eq!(output["unsatisfiable"], serde_json::json!([]));
}

const LARGE_SOURCE: &str = r#"Ontology(
    Declaration(Class(<urn:A>)) Declaration(ObjectProperty(<urn:r>))
    SubClassOf(<urn:A> ObjectMinCardinality(128 <urn:r>))
    SubClassOf(<urn:A> ObjectMaxCardinality(0 <urn:r>)))"#;

#[test]
fn symbolic_nominal_choice_does_not_publish_branch_local_subsumption() {
    let source = r#"Ontology(
        Declaration(Class(<urn:Big>)) Declaration(Class(<urn:Small>))
        Declaration(Class(<urn:Other>)) Declaration(Class(<urn:F>))
        Declaration(ObjectProperty(<urn:r>))
        EquivalentClasses(<urn:Big> ObjectOneOf(<urn:a> <urn:b>))
        EquivalentClasses(<urn:Small> ObjectOneOf(<urn:a>))
        SubClassOf(<urn:Other> ObjectMaxCardinality(128 <urn:r> <urn:F>)))"#;
    let result = classify_mode(source, false, false);
    assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
    let output: serde_json::Value = serde_json::from_slice(&result.stdout).unwrap();
    assert_eq!(output["consistent"], true);
    assert_eq!(output["dropped"], 0);
    let pairs = output["subsumptions"].as_array().unwrap();
    assert!(pairs.contains(&serde_json::json!(["urn:Small", "urn:Big"])));
    assert!(!pairs.contains(&serde_json::json!(["urn:Big", "urn:Small"])),
        "a model choosing a for the Big witness does not entail Big <= Small: {output}");
}

#[test]
fn automatic_large_cardinality_uses_checked_symbolic_source() {
    let result = classify_mode(LARGE_SOURCE, false, false);
    assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
    let output: serde_json::Value = serde_json::from_slice(&result.stdout).unwrap();
    assert_eq!(output["consistent"], true);
    assert_eq!(output["dropped"], 0);
    assert_eq!(output["unsatisfiable"], serde_json::json!(["urn:A"]));
}

#[test]
fn automatic_symbolic_route_respects_requested_runtime_certificate() {
    let result = classify_mode(LARGE_SOURCE, true, false);
    assert!(!result.status.success());
    assert!(String::from_utf8_lossy(&result.stderr).contains("cannot bypass requested HT runtime certification"));
}

#[test]
fn automatic_symbolic_decline_preserves_ordinary_pipeline_coverage() {
    let source = LARGE_SOURCE.replacen("Ontology(",
        "Ontology(Declaration(Class(<urn:B>)) ObjectPropertyDomain(<http://www.w3.org/2002/07/owl#topObjectProperty> <urn:B>)", 1);
    let explicit = classify_mode(&source, false, true);
    assert!(!explicit.status.success());
    assert!(String::from_utf8_lossy(&explicit.stderr).contains("symbolic source bridge deferred"));
    let automatic = classify_mode(&source, false, false);
    assert!(automatic.status.success(), "{}", String::from_utf8_lossy(&automatic.stderr));
    let output: serde_json::Value = serde_json::from_slice(&automatic.stdout).unwrap();
    assert_eq!(output["consistent"], true);
    assert_eq!(output["dropped"], 0);
    assert_eq!(output["unsatisfiable"], serde_json::json!(["urn:A"]));
}
