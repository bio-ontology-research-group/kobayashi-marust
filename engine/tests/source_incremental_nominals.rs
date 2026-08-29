use std::io::Write;
use std::process::{Command, Stdio};

const BEFORE: &str = r#"Prefix(:=<http://example.org/>)
Ontology(
 Declaration(Class(:A)) Declaration(Class(:X)) Declaration(Class(:Y)) Declaration(Class(:Z))
 Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))
 EquivalentClasses(:A ObjectOneOf(:a))
 ClassAssertion(:A :b)
 SameIndividual(:a :b)
 SubClassOf(:X :Y) SubClassOf(:Y :Z) SubClassOf(:Z :X)
)"#;

const AFTER: &str = r#"Prefix(:=<http://example.org/>)
Ontology(
 Declaration(Class(:A)) Declaration(Class(:X)) Declaration(Class(:Y)) Declaration(Class(:Z))
 Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))
 EquivalentClasses(:A ObjectOneOf(:a))
 ClassAssertion(:A :b)
 SameIndividual(:a :b)
 SubClassOf(:X :Y) SubClassOf(:Y :Z) SubClassOf(:Z :X)
 SubClassOf(:X ObjectUnionOf(:Y :Z))
)"#;

#[test]
fn nominal_cb_addition_retains_state_and_equals_fresh_classify() {
    let mut child = Command::new(env!("CARGO_BIN_EXE_km"))
        .arg("incremental-source")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn km incremental-source");
    {
        let stdin = child.stdin.as_mut().expect("incremental stdin");
        for (op, source) in [("init", BEFORE), ("replace", AFTER)] {
            serde_json::to_writer(
                &mut *stdin,
                &serde_json::json!({"op": op, "functional_syntax": source}),
            )
            .unwrap();
            stdin.write_all(b"\n").unwrap();
        }
    }
    let output = child.wait_with_output().expect("wait for source session");
    assert!(
        output.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let rows: Vec<serde_json::Value> = String::from_utf8(output.stdout)
        .unwrap()
        .lines()
        .map(|line| serde_json::from_str(line).unwrap())
        .collect();
    assert_eq!(rows.len(), 2, "rows={rows:#?}");
    assert_eq!(rows[0]["route"], "nominals");
    assert_eq!(rows[0]["retained_backend"], true);
    assert_eq!(rows[1]["receipt"]["strategy"], "cb_delta");
    assert_eq!(rows[1]["receipt"]["meaningful_incremental_update"], true);
    assert!(rows[1]["receipt"]["retained_states"].as_u64().unwrap() > 0);

    let path = std::env::temp_dir().join(format!(
        "km-source-incremental-nominal-{}.ofn",
        std::process::id()
    ));
    std::fs::write(&path, AFTER).unwrap();
    let fresh = Command::new(env!("CARGO_BIN_EXE_km"))
        .arg("classify")
        .arg(&path)
        .output()
        .expect("run fresh km classify");
    let _ = std::fs::remove_file(path);
    assert!(
        fresh.status.success(),
        "fresh stderr: {}",
        String::from_utf8_lossy(&fresh.stderr)
    );
    let fresh_result: serde_json::Value = serde_json::from_slice(&fresh.stdout).unwrap();
    assert_eq!(rows[1]["result"], fresh_result);
}
