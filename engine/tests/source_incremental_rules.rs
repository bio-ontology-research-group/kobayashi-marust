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
        // The legacy per-route adapter session is what these receipts describe.
        .env("KM_SOURCE_SESSION", "legacy")
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
fn isolated_rule_projection_is_rechecked_when_a_named_body_becomes_active() {
    let source = r#"Ontology(
      Declaration(Class(<http://example.org/isolated#A>))
      Declaration(Class(<http://example.org/isolated#B>))
      DisjointClasses(<http://example.org/isolated#A> <http://example.org/isolated#B>)
      Declaration(NamedIndividual(<http://example.org/isolated#a>))
      ClassAssertion(owl:Thing <http://example.org/isolated#a>)
      DLSafeRule(
        Body(ClassAtom(<http://example.org/isolated#A> Variable(<http://example.org/isolated#x>)))
        Head(ClassAtom(<http://example.org/isolated#B> Variable(<http://example.org/isolated#x>))))
    )"#;
    let activated = source.replace(
        "ClassAssertion(owl:Thing",
        "ClassAssertion(<http://example.org/isolated#A>",
    );
    let rows = run_source_commands(&[
        serde_json::json!({"op": "init", "functional_syntax": source}),
        serde_json::json!({"op": "replace", "functional_syntax": activated}),
        serde_json::json!({"op": "replace", "functional_syntax": source}),
    ]);
    assert_eq!(rows.len(), 3, "{rows:#?}");
    assert_eq!(rows[0]["result"]["consistent"], true, "{rows:#?}");
    assert_eq!(rows[1]["result"]["consistent"], false, "{rows:#?}");
    assert_eq!(rows[2]["result"], rows[0]["result"], "{rows:#?}");
}

#[test]
fn rules_route_retains_taxonomy_across_abox_clash_and_retraction() {
    let mut child = Command::new(env!("CARGO_BIN_EXE_km"))
        .arg("incremental-source")
        // The legacy per-route adapter session is what these receipts describe.
        .env("KM_SOURCE_SESSION", "legacy")
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

/// ore_ont_7278-shaped input (`graph_data_rules.ofn`: the graph rules with
/// long bodies over a data ABox). With `KM_DATA_ASSERTION_AS_CLASS=1` a
/// revision that adds one object assertion reaches the incremental rule
/// probe (`ht_delta`). The probe and the batch rule checker use the same join
/// order, so they give the same verdict in comparable time; before, the
/// probe matched these bodies in source order and ran for many minutes.
#[test]
fn incremental_rule_probe_matches_the_batch_checker_on_graph_rules() {
    let source = include_str!("fixtures/graph_data_rules.ofn");
    let axiom = "ObjectPropertyAssertion(<http://ontology.dumontierlab.com/isPartOf> \
        <http://ontology.dumontierlab.com/III_2004> <http://ontology.dumontierlab.com/_2005>)\n";
    let close = source.trim_end().rfind(')').unwrap();
    let revised = format!("{}{}{}", &source[..close], axiom, &source[close..]);

    let dir = std::path::Path::new(env!("CARGO_TARGET_TMPDIR"));
    let path = dir.join(format!("graph-rules-revised-{}.ofn", std::process::id()));
    std::fs::write(&path, &revised).unwrap();
    let started = std::time::Instant::now();
    let mut batch = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars_os() {
        if key.to_string_lossy().starts_with("KM_") {
            batch.env_remove(key);
        }
    }
    let batch = batch
        .env("KM_DATA_ASSERTION_AS_CLASS", "1")
        .args(["classify", "--lines"])
        .arg(&path)
        .output()
        .unwrap();
    let batch_s = started.elapsed().as_secs_f64();
    let _ = std::fs::remove_file(&path);
    assert!(batch.status.success(), "{}", String::from_utf8_lossy(&batch.stderr));
    let batch_out = String::from_utf8(batch.stdout).unwrap();
    let batch_consistent = batch_out
        .lines()
        .find_map(|line| line.strip_prefix("CONSISTENT "))
        .map(|v| v.trim() == "1")
        .expect("batch verdict");

    let mut child = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars_os() {
        if key.to_string_lossy().starts_with("KM_") {
            child.env_remove(key);
        }
    }
    let mut child = child
        .arg("incremental-source")
        .env("KM_SOURCE_SESSION", "legacy")
        .env("KM_DATA_ASSERTION_AS_CLASS", "1")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let mut stdin = child.stdin.take().unwrap();
    let mut stdout = std::io::BufReader::new(child.stdout.take().unwrap());
    let mut rows = Vec::new();
    let mut walls = Vec::new();
    for (op, doc) in [("init", source.to_string()), ("replace", revised)] {
        use std::io::BufRead;
        let started = std::time::Instant::now();
        serde_json::to_writer(&mut stdin, &serde_json::json!({"op": op, "functional_syntax": doc})).unwrap();
        stdin.write_all(b"\n").unwrap();
        stdin.flush().unwrap();
        let mut line = String::new();
        stdout.read_line(&mut line).unwrap();
        walls.push(started.elapsed().as_secs_f64());
        rows.push(serde_json::from_str::<serde_json::Value>(&line).unwrap());
    }
    drop(stdin);
    let output = child.wait_with_output().unwrap();
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    assert_eq!(rows[1]["receipt"]["strategy"], "ht_delta", "{:#?}", rows[1]["receipt"]);
    assert_eq!(rows[1]["result"]["consistent"], batch_consistent, "{rows:#?}");
    // Comparable time: the probe does no more work than the batch checker's
    // rule step (generous for a loaded host).
    assert!(
        walls[1] <= 3.0 * batch_s + 30.0,
        "incremental revision {:.1}s, batch {:.1}s",
        walls[1],
        batch_s
    );
}
