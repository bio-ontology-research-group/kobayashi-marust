use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_FIXTURE: AtomicU64 = AtomicU64::new(0);

fn classify(source: &str) -> (serde_json::Value, String) {
    let path = std::env::temp_dir().join(format!(
        "km-certified-abox-production-{}-{}.ofn",
        std::process::id(),
        NEXT_FIXTURE.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::write(&path, source).expect("write ontology fixture");
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    command.arg("classify").arg(&path);
    for (key, _) in std::env::vars() {
        if key.starts_with("KM_") {
            command.env_remove(key);
        }
    }
    command.env("KM_ABOX_PRODUCTION_TRACE", "1");
    command.env("KM_NOMINAL_HT_PROBE_TRACE", "1");
    let output = command.output().expect("run automatic classification");
    let _ = std::fs::remove_file(path);
    assert!(
        output.status.success(),
        "status={:?} stderr={}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
    (
        serde_json::from_slice(&output.stdout).expect("classification JSON"),
        String::from_utf8(output.stderr).expect("UTF-8 stderr"),
    )
}

#[test]
fn expressive_class_identity_abox_uses_complete_general_ht_probe() {
    let (result, stderr) = classify(
        r#"Prefix(:=<http://example.org/>)
Ontology(
 Declaration(Class(:A)) Declaration(Class(:B))
 Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:s))
 Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))
 SubClassOf(:A ObjectMinCardinality(2 :r :B))
 InverseObjectProperties(:r :s)
 ClassAssertion(:A :a)
 ClassAssertion(:B :b)
 DifferentIndividuals(:a :b)
)"#,
    );
    assert_eq!(result["consistent"], true);
    assert!(
        stderr.contains("KM_NOMINAL_HT_PROBE result=accepted"),
        "automatic route did not publish through the complete general HT probe: {stderr}"
    );
}

#[test]
fn certified_abox_completion_restores_absorbed_tbox_schedule() {
    let (result, stderr) = classify(
        r#"Prefix(:=<http://example.org/>)
Ontology(
 Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C))
 Declaration(ObjectProperty(:r))
 Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))
 SubClassOf(:A :B)
 SubClassOf(ObjectIntersectionOf(:B :C) owl:Nothing)
 SubClassOf(ObjectOneOf(:a) ObjectOneOf(:a))
 ClassAssertion(:A :a)
 ObjectPropertyAssertion(:r :a :b)
 DifferentIndividuals(:a :b)
)"#,
    );
    assert_eq!(result["consistent"], true);
    assert!(result["subsumptions"]
        .as_array()
        .unwrap()
        .iter()
        .any(|pair| pair[0] == ":A" && pair[1] == ":B"));
    assert!(
        stderr.contains("KM_ABOX_PRODUCTION result=accepted"),
        "automatic route did not publish through the certified production probe: {stderr}"
    );
}

#[test]
fn certified_abox_completion_detects_joint_class_clash() {
    let (result, stderr) = classify(
        r#"Prefix(:=<http://example.org/>)
Ontology(
 Declaration(Class(:A)) Declaration(Class(:B))
 Declaration(ObjectProperty(:r))
 Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))
 SubClassOf(ObjectIntersectionOf(:A :B) owl:Nothing)
 SubClassOf(ObjectOneOf(:a) ObjectOneOf(:a))
 ClassAssertion(:A :a) ClassAssertion(:B :a)
 ObjectPropertyAssertion(:r :a :b)
 DifferentIndividuals(:a :b)
)"#,
    );
    assert_eq!(result["consistent"], false);
    assert!(stderr.contains("KM_ABOX_PRODUCTION result=accepted"));
}

#[test]
fn unsupported_probe_restores_exact_nominal_route() {
    let (result, stderr) = classify(
        r#"Prefix(:=<http://example.org/>)
Ontology(
 Declaration(Class(:A)) Declaration(Class(:B))
 Declaration(ObjectProperty(:r))
 Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))
 SubClassOf(:A :B)
 ObjectPropertyRange(:r :B)
 SubClassOf(ObjectOneOf(:a) ObjectOneOf(:a))
 ClassAssertion(:A :a)
 ObjectPropertyAssertion(:r :a :b)
 DifferentIndividuals(:a :b)
)"#,
    );
    assert_eq!(result["consistent"], true);
    assert!(result["subsumptions"]
        .as_array()
        .unwrap()
        .iter()
        .any(|pair| pair[0] == ":A" && pair[1] == ":B"));
    assert!(
        stderr.contains("KM_ABOX_PRODUCTION result=declined"),
        "unsupported normalized input did not decline before nominal fallback: {stderr}"
    );
}
