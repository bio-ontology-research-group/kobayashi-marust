use std::path::Path;
use std::process::{Command, Output};

fn run_explain(args: &[&str]) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    command.arg("explain").args(args);
    for (key, _) in std::env::vars() {
        if key.starts_with("KM_") {
            command.env_remove(key);
        }
    }
    command
        .env("KM_ROUTE", "ht_qo")
        .env("KM_THREADS", "1")
        .env("KM_TIMING", "1")
        .output()
        .unwrap()
}

fn temporary_ontology(name: &str, source: &str) -> std::path::PathBuf {
    let path =
        std::env::temp_dir().join(format!("km-explain-cli-{}-{name}.ofn", std::process::id()));
    std::fs::write(&path, source).unwrap();
    path
}

#[test]
fn el_route_enumerates_two_verified_source_axiom_justifications() {
    let ontology = temporary_ontology(
        "el-two-justifications",
        r#"Prefix(:=<http://example.org/>)
Ontology(
SubClassOf(:A :B)
SubClassOf(:B :D)
SubClassOf(:A :C)
SubClassOf(:C :D)
SubClassOf(:Noise :D)
)"#,
    );

    let output = run_explain(&[
        "--route",
        "auto",
        "--max-axioms",
        "8",
        "--max-checks",
        "64",
        "--max-justifications",
        "2",
        ontology.to_str().unwrap(),
        "subclass",
        "http://example.org/A",
        "http://example.org/D",
    ]);

    assert!(
        output.status.success(),
        "km explain failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("in-process elc done"),
        "EL explanation did not exercise the EL mechanism: {stderr}"
    );
    let report: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(report["schemaVersion"], 2);
    assert_eq!(report["status"], "entailed");
    assert_eq!(report["oracleSubsetMinimal"], true);
    assert_eq!(report["justifications"].as_array().unwrap().len(), 2);
    assert_eq!(report["justificationLimitReached"], true);
    assert_eq!(report["enumerationComplete"], false);
    assert_eq!(
        report["prefixDeclarations"][0],
        "Prefix(:=<http://example.org/>)"
    );
    for justification in report["justifications"].as_array().unwrap() {
        assert_eq!(justification["axiomCount"], 2);
        assert_eq!(justification["verified"], true);
        assert_eq!(justification["subsetMinimal"], true);
        assert!(!justification["axioms"]
            .as_array()
            .unwrap()
            .iter()
            .any(|axiom| axiom["functionalSyntax"]
                .as_str()
                .unwrap()
                .contains("Noise")));
    }

    let unsafe_route = run_explain(&[
        "--route",
        "ht_qo",
        ontology.to_str().unwrap(),
        "inconsistent",
    ]);
    let _ = std::fs::remove_file(&ontology);
    assert_eq!(unsafe_route.status.code(), Some(3));
    assert!(unsafe_route.stdout.is_empty());
    assert!(String::from_utf8_lossy(&unsafe_route.stderr)
        .contains("not an explanation-safe production oracle"));
}

#[test]
fn cb_route_explains_an_inverse_role_entailment() {
    let ontology = temporary_ontology(
        "cb-inverse",
        r#"Prefix(:=<http://example.org/>)
Ontology(
InverseObjectProperties(:r :s)
ObjectPropertyRange(:s :B)
SubClassOf(:A ObjectSomeValuesFrom(:r :C))
)"#,
    );
    let output = run_explain(&[
        "--max-axioms",
        "8",
        "--max-checks",
        "32",
        ontology.to_str().unwrap(),
        "subclass",
        "http://example.org/A",
        "http://example.org/B",
    ]);
    let _ = std::fs::remove_file(&ontology);
    assert!(
        output.status.success(),
        "KM CB explanation failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("in-process engine done"),
        "CB explanation did not exercise the CB mechanism: {stderr}"
    );
    let report: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(report["status"], "entailed");
    assert_eq!(report["justifications"][0]["verified"], true);
    assert_eq!(report["justifications"][0]["subsetMinimal"], true);
}

#[test]
fn ht_rules_route_explains_inconsistency_through_the_automatic_gate() {
    let ontology =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/explain_rule_unsat.ofn");
    let output = run_explain(&[
        "--max-axioms",
        "32",
        "--max-checks",
        "96",
        ontology.to_str().unwrap(),
        "inconsistent",
    ]);
    assert!(
        output.status.success(),
        "KM HT explanation failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("route=ht_rules"), "stderr: {stderr}");
    assert!(
        stderr.contains("rules-consistency done") && stderr.contains("consistent=false"),
        "HT explanation did not exercise the validated rule mechanism: {stderr}"
    );
    let report: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(report["status"], "entailed");
    assert_eq!(report["justifications"][0]["verified"], true);
    assert_eq!(report["justifications"][0]["subsetMinimal"], true);
}
