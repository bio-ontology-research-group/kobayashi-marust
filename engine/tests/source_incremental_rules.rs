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
