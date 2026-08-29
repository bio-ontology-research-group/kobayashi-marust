use std::io::Write;
use std::process::{Command, Stdio};

const CONSISTENT: &str = r#"Prefix(:=<http://example.org/rules#>)
Ontology(
 Declaration(Class(:A))
 Declaration(Class(:B))
 Declaration(Class(:C))
 Declaration(NamedIndividual(:a))
 SubClassOf(:A :B)
 DisjointClasses(:B :C)
 ClassAssertion(:A :a)
 DLSafeRule(
   Body(ClassAtom(:A Variable(:x)))
   Head(ClassAtom(:B Variable(:x))))
)"#;

const INCONSISTENT: &str = r#"Prefix(:=<http://example.org/rules#>)
Ontology(
 Declaration(Class(:A))
 Declaration(Class(:B))
 Declaration(Class(:C))
 Declaration(NamedIndividual(:a))
 SubClassOf(:A :B)
 DisjointClasses(:B :C)
 ClassAssertion(:A :a)
 DLSafeRule(
   Body(ClassAtom(:A Variable(:x)))
   Head(ClassAtom(:B Variable(:x))))
 DLSafeRule(
   Body(ClassAtom(:A Variable(:x)))
   Head(ClassAtom(:C Variable(:x))))
)"#;

const MIGRATION_EL: &str = r#"Prefix(:=<http://example.org/migrate#>)
Ontology(
 Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C))
 Declaration(Class(:D)) Declaration(NamedIndividual(:a))
 SubClassOf(:A :B) SubClassOf(:C owl:Nothing)
)"#;

const MIGRATION_RULES: &str = r#"Prefix(:=<http://example.org/migrate#>)
Ontology(
 Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C))
 Declaration(Class(:D)) Declaration(NamedIndividual(:a))
 SubClassOf(:A :B) SubClassOf(:C owl:Nothing) ClassAssertion(:A :a)
 DLSafeRule(
   Body(ClassAtom(:A Variable(:x)))
   Head(ClassAtom(:B Variable(:x))))
)"#;

const MIGRATION_RULES_INCONSISTENT: &str = r#"Prefix(:=<http://example.org/migrate#>)
Ontology(
 Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C))
 Declaration(Class(:D)) Declaration(NamedIndividual(:a))
 SubClassOf(:A :B) SubClassOf(:C owl:Nothing) ClassAssertion(:A :a)
 DLSafeRule(
   Body(ClassAtom(:A Variable(:x)))
   Head(ClassAtom(:B Variable(:x))))
 DLSafeRule(
   Body(ClassAtom(:A Variable(:x)))
   Head(ClassAtom(:C Variable(:x))))
)"#;

const MIGRATION_EL_EXTENDED: &str = r#"Prefix(:=<http://example.org/migrate#>)
Ontology(
 Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C))
 Declaration(Class(:D)) Declaration(NamedIndividual(:a))
 SubClassOf(:A :B) SubClassOf(:C owl:Nothing) SubClassOf(:B :D)
)"#;

fn run_source_commands(commands: &[serde_json::Value]) -> Vec<serde_json::Value> {
    let mut child = Command::new(env!("CARGO_BIN_EXE_km"))
        .arg("incremental-source")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn km incremental-source");
    {
        let stdin = child.stdin.as_mut().expect("incremental stdin");
        for command in commands {
            serde_json::to_writer(&mut *stdin, command).unwrap();
            stdin.write_all(b"\n").unwrap();
        }
    }
    let output = child.wait_with_output().expect("wait for source session");
    assert!(
        output.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout)
        .unwrap()
        .lines()
        .map(|line| serde_json::from_str(line).unwrap())
        .collect()
}

#[test]
fn rules_route_retains_taxonomy_across_abox_clash_and_retraction() {
    let mut child = Command::new(env!("CARGO_BIN_EXE_km"))
        .arg("incremental-source")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn km incremental-source");
    {
        let stdin = child.stdin.as_mut().expect("incremental stdin");
        for (op, source) in [
            ("init", CONSISTENT),
            ("replace", INCONSISTENT),
            ("replace", CONSISTENT),
        ] {
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
    assert_eq!(rows.len(), 3, "rows={rows:#?}");
    assert_eq!(rows[0]["route"], "ht_rules");
    assert_eq!(rows[0]["retained_backend"], true);
    assert_eq!(rows[0]["result"]["consistent"], true);
    for row in &rows[1..] {
        assert_eq!(row["receipt"]["strategy"], "ht_delta", "row={row:#?}");
        assert_eq!(
            row["receipt"]["meaningful_incremental_update"], true,
            "row={row:#?}"
        );
    }
    assert_eq!(rows[1]["result"]["consistent"], false);
    assert_eq!(rows[1]["receipt"]["added_rules"], 1);
    assert_eq!(rows[2]["receipt"]["removed_rules"], 1);
    assert_eq!(rows[2]["result"]["consistent"], true);
    assert_eq!(rows[2]["result"], rows[0]["result"]);
    assert!(
        rows[2]["result"]["subsumptions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|pair| {
                (pair[0] == "http://example.org/rules#A" || pair[0] == ":A")
                    && (pair[1] == "http://example.org/rules#B" || pair[1] == ":B")
            }),
        "restored row={:#?}",
        rows[2]
    );
}

#[test]
fn source_session_migrates_el_rules_el_and_rolls_back_a_declined_revision() {
    let commands = [
        serde_json::json!({"op": "init", "functional_syntax": MIGRATION_EL}),
        serde_json::json!({"op": "replace", "functional_syntax": MIGRATION_RULES}),
        serde_json::json!({"op": "replace", "functional_syntax": MIGRATION_RULES_INCONSISTENT}),
        serde_json::json!({"op": "replace", "functional_syntax": "Ontology(SubClassOf(<A>"}),
        serde_json::json!({"op": "classify"}),
        serde_json::json!({"op": "replace", "functional_syntax": MIGRATION_RULES}),
        serde_json::json!({"op": "replace", "functional_syntax": MIGRATION_EL}),
        serde_json::json!({"op": "replace", "functional_syntax": MIGRATION_EL_EXTENDED}),
    ];
    let rows = run_source_commands(&commands);
    assert_eq!(rows.len(), 8, "rows={rows:#?}");
    assert_eq!(rows[0]["route"], "elc");

    assert_eq!(rows[1]["receipt"]["route_migrated"], true);
    assert_eq!(rows[1]["receipt"]["route_before"], "elc");
    assert_eq!(rows[1]["receipt"]["route_after"], "ht_rules");
    assert_eq!(rows[1]["receipt"]["strategy"], "exact_rebuild");
    assert_eq!(rows[1]["receipt"]["meaningful_incremental_update"], false);
    assert_eq!(rows[1]["retained_backend"], true);

    assert_eq!(rows[2]["receipt"]["strategy"], "ht_delta");
    assert_eq!(rows[2]["receipt"]["meaningful_incremental_update"], true);
    assert_eq!(rows[2]["result"]["consistent"], false);
    assert_eq!(rows[2]["revision"], 2);

    assert_eq!(rows[3]["status"], "error");
    assert_eq!(rows[4]["status"], "ok");
    assert_eq!(rows[4]["route"], "ht_rules");
    assert_eq!(rows[4]["revision"], 2);
    assert_eq!(rows[4]["result"], rows[2]["result"]);

    assert_eq!(rows[5]["receipt"]["strategy"], "ht_delta");
    assert_eq!(rows[5]["receipt"]["meaningful_incremental_update"], true);
    assert_eq!(rows[5]["result"]["consistent"], true);

    assert_eq!(rows[6]["receipt"]["route_migrated"], true);
    assert_eq!(rows[6]["receipt"]["route_before"], "ht_rules");
    assert_eq!(rows[6]["receipt"]["route_after"], "elc");
    assert_eq!(rows[6]["receipt"]["strategy"], "exact_rebuild");
    assert_eq!(rows[6]["retained_backend"], true);

    assert_eq!(rows[7]["receipt"]["strategy"], "el_delta");
    assert_eq!(rows[7]["receipt"]["meaningful_incremental_update"], true);
    let fresh = run_source_commands(&[serde_json::json!({
        "op": "init",
        "functional_syntax": MIGRATION_EL_EXTENDED
    })]);
    assert_eq!(rows[7]["result"], fresh[0]["result"]);
}
