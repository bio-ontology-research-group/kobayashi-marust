use std::io::Write;
use std::process::{Command, Stdio};

const WIRE: &str = r#"{
  "concepts":["A","B"],
  "roles":[],
  "clauses":[],
  "queries":[0,1],
  "inverse":false,
  "number":false,
  "nominals":[],
  "native_abox":{},
  "card_defs":[],
  "chains":[],
  "transitive":[]
}"#;

const MIXED_WIRE: &str = r#"{
  "concepts":["A","B","Dormant"],
  "roles":[],
  "clauses":[{
    "body":[{"k":"c","neg":false,"c":2,"t":0},{"k":"eq","s":0,"t":0}],
    "head":[{"k":"c","neg":false,"c":0,"t":0}]
  }],
  "queries":[0,1],
  "inverse":false,
  "number":false,
  "nominals":[],
  "native_abox":{},
  "card_defs":[],
  "chains":[],
  "transitive":[]
}"#;

const ROLE_CHAIN_WIRE: &str = r#"{
  "concepts":["A","B","C","D"],
  "roles":["r0","r1","r2"],
  "clauses":[
    {"body":[{"k":"c","neg":false,"c":0,"t":0}],"head":[{"k":"e","r":0,"neg":false,"c":1,"t":0}]},
    {"body":[{"k":"c","neg":false,"c":1,"t":0}],"head":[{"k":"e","r":1,"neg":false,"c":3,"t":0}]},
    {"body":[{"k":"c","neg":false,"c":0,"t":0},{"k":"r","r":2,"s":0,"t":1}],"head":[{"k":"c","neg":false,"c":2,"t":1}]},
    {"body":[{"k":"c","neg":false,"c":3,"t":0}],"head":[{"k":"c","neg":true,"c":2,"t":0}]}
  ],
  "queries":[0,1,2,3],
  "inverse":false,
  "number":false,
  "nominals":[],
  "native_abox":{},
  "card_defs":[],
  "chains":[[0,1,2]],
  "transitive":[0]
}"#;

const CARDINALITY_SIDE_WIRE: &str = r#"{
  "concepts":["AtLeastTwo","Filler"],
  "roles":["r"],
  "clauses":[],
  "queries":[0,1],
  "inverse":false,
  "number":true,
  "nominals":[],
  "native_abox":{},
  "card_defs":[{"marker":0,"min":true,"n":2,"role":0,"filler":1}],
  "chains":[],
  "transitive":[]
}"#;

fn run_with_input(
    input: &str,
    global_checker: &str,
    taxonomy_checker: &str,
    output_stem: &str,
) -> std::process::Output {
    let root = std::env::temp_dir().join(format!(
        "km-ht-taxonomy-runtime-{}-{output_stem}",
        std::process::id()
    ));
    let global_out = root.with_extension("global.json");
    let taxonomy_out = root.with_extension("taxonomy.json");
    let mut child = Command::new(env!("CARGO_BIN_EXE_tableau_cli"))
        .env("KM_HT", "1")
        .env("KM_HT_FORCE", "1")
        .env("KM_HT_GLOBAL", "1")
        // Certification must select the exact source calculus even when the
        // ordinary performance route requests harvested consequences.
        .env("KM_HT_HARVEST", "1")
        .env("KM_HT_LEAN_CERT_CHECKER", global_checker)
        .env("KM_HT_LEAN_TAXONOMY_CERT_CHECKER", taxonomy_checker)
        .env("KM_HT_LEAN_CERT_OUT", &global_out)
        .env("KM_HT_LEAN_TAXONOMY_CERT_OUT", &taxonomy_out)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn tableau worker");
    child
        .stdin
        .take()
        .expect("tableau stdin")
        .write_all(input.as_bytes())
        .expect("write tableau wire input");
    let output = child.wait_with_output().expect("wait for tableau worker");
    assert!(global_out.is_file(), "global certificate must be persisted");
    assert!(
        taxonomy_out.is_file(),
        "taxonomy certificate must be persisted"
    );
    let _ = std::fs::remove_file(global_out);
    let _ = std::fs::remove_file(taxonomy_out);
    output
}

fn run(global_checker: &str, taxonomy_checker: &str, output_stem: &str) -> std::process::Output {
    run_with_input(WIRE, global_checker, taxonomy_checker, output_stem)
}

#[test]
fn accepted_complete_taxonomy_is_the_published_classification() {
    let global_checker =
        std::env::var("KM_HT_TEST_LEAN_GLOBAL_CHECKER").unwrap_or_else(|_| "/bin/true".to_string());
    let taxonomy_checker = std::env::var("KM_HT_TEST_LEAN_TAXONOMY_CHECKER")
        .unwrap_or_else(|_| "/bin/true".to_string());
    let output = run(&global_checker, &taxonomy_checker, "accept");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let value: serde_json::Value =
        serde_json::from_slice(&output.stdout).expect("classification is JSON");
    assert_eq!(value["consistent"], true);
    assert_eq!(value["unsatisfiable"], serde_json::json!([]));
    assert_eq!(
        value["subsumptions"],
        serde_json::json!([["A", "A"], ["B", "B"]])
    );
}

#[test]
fn rejecting_taxonomy_checker_suppresses_publication() {
    let output = run("/bin/true", "/bin/false", "reject");
    assert!(!output.status.success());
    assert!(
        output.stdout.is_empty(),
        "unchecked classification was published"
    );
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("rejected the certificate"),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn accepted_mixed_taxonomy_is_read_from_wrapped_evidence() {
    let global_checker =
        std::env::var("KM_HT_TEST_LEAN_GLOBAL_CHECKER").unwrap_or_else(|_| "/bin/true".to_string());
    let taxonomy_checker = std::env::var("KM_HT_TEST_LEAN_TAXONOMY_CHECKER")
        .unwrap_or_else(|_| "/bin/true".to_string());
    let output = run_with_input(
        MIXED_WIRE,
        &global_checker,
        &taxonomy_checker,
        "mixed-accept",
    );
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let value: serde_json::Value =
        serde_json::from_slice(&output.stdout).expect("classification is JSON");
    assert_eq!(value["consistent"], true);
    assert_eq!(value["unsatisfiable"], serde_json::json!([]));
    assert_eq!(
        value["subsumptions"],
        serde_json::json!([["A", "A"], ["B", "B"]])
    );
}

#[test]
fn certified_taxonomy_restores_and_checks_raw_role_chain_axioms() {
    let global_checker = std::env::var("KM_HT_TEST_LEAN_GLOBAL_CHECKER")
        .or_else(|_| std::env::var("KM_HT_TEST_LEAN_CHECKER"))
        .unwrap_or_else(|_| "/bin/true".to_string());
    let taxonomy_checker = std::env::var("KM_HT_TEST_LEAN_TAXONOMY_CHECKER")
        .unwrap_or_else(|_| "/bin/true".to_string());
    let output = run_with_input(
        ROLE_CHAIN_WIRE,
        &global_checker,
        &taxonomy_checker,
        "raw-role-chain",
    );
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let value: serde_json::Value =
        serde_json::from_slice(&output.stdout).expect("classification is JSON");
    assert_eq!(value["consistent"], true);
    assert!(value["unsatisfiable"]
        .as_array()
        .expect("unsatisfiable array")
        .contains(&serde_json::json!("A")));
}

#[test]
fn first_class_cardinality_side_data_fails_closed_before_publication() {
    let mut child = Command::new(env!("CARGO_BIN_EXE_tableau_cli"))
        .env("KM_HT", "1")
        .env("KM_HT_FORCE", "1")
        .env("KM_HT_GLOBAL", "1")
        .env("KM_HT_LEAN_CERT_CHECKER", "/bin/true")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn tableau worker");
    child
        .stdin
        .take()
        .expect("tableau stdin")
        .write_all(CARDINALITY_SIDE_WIRE.as_bytes())
        .expect("write cardinality wire input");
    let output = child.wait_with_output().expect("wait for tableau worker");
    assert!(!output.status.success());
    assert!(output.stdout.is_empty(), "unchecked result was published");
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("does not yet cover first-class number-restriction side data"),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}
