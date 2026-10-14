//! The retained source session reuses stored answers (exact revisions and
//! ⊥-locality deletion reuse) and must publish exactly what a fresh
//! `km classify` publishes for every revision.
use std::collections::BTreeSet;
use std::io::Write;
use std::process::{Command, Stdio};

const HEADER: &str = "Prefix(:=<http://example.org/m#>)\nOntology(<http://example.org/m>\n";

fn ontology(axioms: &[&str]) -> String {
    let mut text = String::from(HEADER);
    for name in ["A", "B", "C", "D", "E", "F", "G", "H", "K"] {
        text.push_str(&format!("Declaration(Class(:{name}))\n"));
    }
    text.push_str("Declaration(ObjectProperty(:r))\nDeclaration(NamedIndividual(:a))\n");
    for axiom in axioms {
        text.push_str(axiom);
        text.push('\n');
    }
    text.push_str(")\n");
    text
}

/// Consistency, unsatisfiable classes, and subsumptions between satisfiable
/// classes: the relation the benchmark fingerprint compares.
fn canonical(result: &serde_json::Value) -> (bool, BTreeSet<String>, BTreeSet<(String, String)>) {
    let consistent = result["consistent"].as_bool().unwrap();
    let unsat: BTreeSet<String> = result["unsatisfiable"]
        .as_array()
        .unwrap()
        .iter()
        .map(|v| v.as_str().unwrap().to_string())
        .collect();
    let pairs = result["subsumptions"]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| (p[0].as_str().unwrap().to_string(), p[1].as_str().unwrap().to_string()))
        .filter(|(a, b)| !unsat.contains(a) && !unsat.contains(b) && a != b)
        .collect();
    (consistent, unsat, pairs)
}

static FRESH: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

fn fresh(source: &str, tag: usize) -> serde_json::Value {
    // Tests run in parallel threads of one process: keep every file unique.
    let unique = FRESH.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!("km-module-reuse-{}-{tag}-{unique}.ofn", std::process::id()));
    std::fs::write(&path, source).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_km"))
        .arg("classify")
        .arg(&path)
        .env("KM_ROUTE", "auto")
        .output()
        .expect("run fresh km classify");
    let _ = std::fs::remove_file(path);
    assert!(output.status.success(), "fresh stderr: {}", String::from_utf8_lossy(&output.stderr));
    serde_json::from_slice(&output.stdout).unwrap()
}

fn session(revisions: &[String]) -> Vec<serde_json::Value> {
    let mut child = Command::new(env!("CARGO_BIN_EXE_km"))
        .arg("incremental-source")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn km incremental-source");
    {
        let stdin = child.stdin.as_mut().unwrap();
        for (index, source) in revisions.iter().enumerate() {
            let op = if index == 0 { "init" } else { "replace" };
            serde_json::to_writer(&mut *stdin, &serde_json::json!({"op": op, "functional_syntax": source}))
                .unwrap();
            stdin.write_all(b"\n").unwrap();
        }
    }
    let output = child.wait_with_output().unwrap();
    assert!(output.status.success(), "stderr: {}", String::from_utf8_lossy(&output.stderr));
    String::from_utf8(output.stdout)
        .unwrap()
        .lines()
        .map(|line| serde_json::from_str(line).unwrap())
        .collect()
}

fn check(revisions: Vec<String>, strategies: &[&str]) {
    let rows = session(&revisions);
    assert_eq!(rows.len(), revisions.len(), "rows={rows:#?}");
    for (index, (row, source)) in rows.iter().zip(&revisions).enumerate() {
        assert_eq!(row["status"], "ok", "row {index}: {row:#?}");
        assert_eq!(row["receipt"]["strategy"], strategies[index], "row {index}: {:#?}", row["receipt"]);
        assert_eq!(canonical(&row["result"]), canonical(&fresh(source, index)), "revision {index}");
    }
}

#[test]
fn deletion_reuses_unaffected_rows_and_restoration_is_exact() {
    let base = [
        "SubClassOf(:B :A)",
        "SubClassOf(:C :B)",
        "SubClassOf(:D ObjectSomeValuesFrom(:r :C))",
        "EquivalentClasses(:E ObjectSomeValuesFrom(:r :A))",
        "SubClassOf(:F :G)",
        "SubClassOf(:H :F)",
        "DisjointClasses(:K :A)",
        "SubClassOf(:K :C)",
        "ClassAssertion(:G :a)",
    ];
    let original = ontology(&base);
    // Removing C ⊑ B changes C, D (via E), K (no longer unsatisfiable).
    let deleted = ontology(&[base[0], base[2], base[3], base[4], base[5], base[6], base[7], base[8]]);
    // Removing F ⊑ G affects only H and F.
    let unrelated = ontology(&[base[0], base[1], base[2], base[3], base[5], base[6], base[7], base[8]]);
    check(
        vec![original.clone(), deleted, original.clone(), unrelated, original],
        &["full_classify", "module_reuse", "exact_reuse", "module_reuse", "exact_reuse"],
    );
}

#[test]
fn nominal_abox_deletion_and_additions_stay_exact() {
    let base = [
        "SubClassOf(:B :A)",
        "EquivalentClasses(:C ObjectHasValue(:r :a))",
        "SubClassOf(:D :C)",
        "ClassAssertion(:D :a)",
        "SubClassOf(:E ObjectSomeValuesFrom(:r ObjectOneOf(:a)))",
    ];
    let original = ontology(&base);
    let deleted = ontology(&[base[0], base[1], base[2], base[4]]);
    let added = ontology(&[base[0], base[1], base[2], base[3], base[4], "SubClassOf(:A :F)"]);
    let rows = session(&[original.clone(), deleted.clone(), added.clone(), original.clone()]);
    for (index, (row, source)) in rows.iter().zip([&original, &deleted, &added, &original]).enumerate() {
        assert_eq!(row["status"], "ok", "row {index}: {row:#?}");
        assert_eq!(canonical(&row["result"]), canonical(&fresh(source, 10 + index)), "revision {index}");
    }
    assert_eq!(rows[2]["receipt"]["strategy"], "full_classify");
    assert_eq!(rows[3]["receipt"]["strategy"], "exact_reuse");
}

#[test]
fn deletion_of_an_unsatisfiable_cause_reclassifies_the_subject() {
    let base = [
        "SubClassOf(:A :B)",
        "DisjointClasses(:B :C)",
        "SubClassOf(:A :C)",
        "SubClassOf(:D :A)",
        "SubClassOf(:E :F)",
    ];
    let original = ontology(&base);
    let deleted = ontology(&[base[0], base[1], base[3], base[4]]);
    check(vec![original.clone(), deleted, original], &["full_classify", "module_reuse", "exact_reuse"]);
}

#[test]
fn nominal_tbox_deletion_reclassifies_only_nominal_and_affected_subjects() {
    let base = [
        "SubClassOf(:B :A)",
        "EquivalentClasses(:C ObjectHasValue(:r :a))",
        "SubClassOf(:D :C)",
        "SubClassOf(:E ObjectSomeValuesFrom(:r ObjectOneOf(:a)))",
        "SubClassOf(:H :F)",
        "SubClassOf(:F :G)",
        "ClassAssertion(:B :a)",
        "ClassAssertion(:K :a)",
    ];
    let original = ontology(&base);
    // An assertion: the nominal subjects (C, D, E) are reclassified on the
    // complete revision, the nominal-free rows are reused.
    let assertion = ontology(&[base[0], base[1], base[2], base[3], base[4], base[5], base[6]]);
    // A nominal-free TBox axiom outside the empty-signature module of the
    // assertion-keeping index: the plain module path.
    let tbox = ontology(&[base[0], base[1], base[2], base[3], base[4], base[6], base[7]]);
    check(
        vec![original.clone(), assertion, original.clone(), tbox, original],
        &["full_classify", "subject_reuse", "exact_reuse", "module_reuse", "exact_reuse"],
    );
}

#[test]
fn global_nominal_axioms_keep_exact_answers() {
    // ⊤ ⊑ ∃r.{a} with r inverse-functional collapses the domain. In the
    // nominal TBox index that axiom is never local, so every subject would be
    // affected; the assertion-keeping index puts the deleted assertion only
    // into the modules of classes over its signature. Answers equal cold.
    let base = [
        "SubClassOf(ObjectUnionOf(:A ObjectComplementOf(:A)) ObjectSomeValuesFrom(:r ObjectOneOf(:a)))",
        "InverseFunctionalObjectProperty(:r)",
        "SubClassOf(:B :C)",
        "ClassAssertion(:B :a)",
        "ClassAssertion(ObjectComplementOf(:D) :a)",
    ];
    let original = ontology(&base);
    let deleted = ontology(&[base[0], base[1], base[2], base[3]]);
    let rows = session(&[original.clone(), deleted.clone(), original.clone()]);
    for (index, (row, source)) in rows.iter().zip([&original, &deleted, &original]).enumerate() {
        assert_eq!(row["status"], "ok", "row {index}: {row:#?}");
        assert_eq!(canonical(&row["result"]), canonical(&fresh(source, 20 + index)), "revision {index}");
    }
    // The assertion-keeping index localises the deleted assertion; the
    // nominal TBox index alone would mark every subject.
    assert_eq!(rows[1]["receipt"]["strategy"], "module_reuse");
    assert_eq!(rows[2]["receipt"]["strategy"], "exact_reuse");
}
