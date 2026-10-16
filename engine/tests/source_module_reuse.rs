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

#[test]
fn successive_independent_deletions_retain_the_previous_exact_base() {
    let base = [
        "SubClassOf(:A :B)", "SubClassOf(:B :C)",
        "SubClassOf(:D :E)", "SubClassOf(:E :F)",
        "SubClassOf(:G :H)", "SubClassOf(:H :K)",
    ];
    let original = ontology(&base);
    let first = ontology(&[base[0], base[2], base[3], base[4], base[5]]);
    let second = ontology(&[base[0], base[2], base[4], base[5]]);
    let revisions = [original.clone(), first.clone(), second, first, original];
    let rows = session(&revisions);
    assert_eq!(rows.len(), revisions.len());
    for (i, (row, source)) in rows.iter().zip(&revisions).enumerate() {
        assert_eq!(row["status"], "ok", "revision {i}: {row:#?}");
        assert_eq!(canonical(&row["result"]), canonical(&fresh(source, 100 + i)), "revision {i}");
    }
    for row in &rows[1..=2] {
        assert_eq!(row["receipt"]["strategy"], "module_reuse");
        assert_eq!(row["receipt"]["removed_axioms"], 1);
        assert_eq!(row["receipt"]["affected_subjects"], 2);
        assert_eq!(row["receipt"]["reclassified_subjects"], 2);
        assert_eq!(row["receipt"]["module_axioms"], 1);
        // The immutable original index is shared, not rebuilt after deletion.
        assert_eq!(row["receipt"]["index_axioms"], 6);
    }
    let first_base = rows[1]["receipt"]["base_revision_statements"].as_u64().unwrap();
    assert_eq!(rows[2]["receipt"]["base_revision_statements"], first_base - 1);
    assert_eq!(rows[1]["receipt"]["reused_subjects"], 4);
    assert_eq!(rows[2]["receipt"]["reused_subjects"], 3);
    assert_eq!(rows[3]["receipt"]["strategy"], "exact_reuse");
    assert_eq!(rows[4]["receipt"]["strategy"], "exact_reuse");
}

#[test]
fn successive_deletions_mask_all_original_told_supports() {
    let base = [
        "SubClassOf(:A :B)", "SubClassOf(:B :D)",
        "SubClassOf(:A :D)", "SubClassOf(:D :C)",
        "SubClassOf(:E :F)",
    ];
    let original = ontology(&base);
    let first = ontology(&base[1..]);
    let second = ontology(&[base[1], base[3], base[4]]);
    let revisions = [original, first, second];
    let rows = session(&revisions);
    assert_eq!(rows.len(), revisions.len());
    for (i, (row, source)) in rows.iter().zip(&revisions).enumerate() {
        assert_eq!(row["status"], "ok", "revision {i}: {row:#?}");
        assert_eq!(canonical(&row["result"]), canonical(&fresh(source, 110 + i)), "revision {i}");
    }
    assert_eq!(rows[2]["receipt"]["strategy"], "module_reuse");
    assert_eq!(rows[2]["receipt"]["removed_axioms"], 1);
    assert_eq!(rows[2]["receipt"]["reclassified_subjects"], 1);
    let (_, _, prior_pairs) = canonical(&rows[1]["result"]);
    assert!(prior_pairs.contains(&(":A".into(), ":D".into())));
    assert!(prior_pairs.contains(&(":A".into(), ":C".into())));
    let (_, _, pairs) = canonical(&rows[2]["result"]);
    // Neither the original A->B->D support nor A->D remains live.
    assert!(!pairs.contains(&(":A".into(), ":D".into())));
    assert!(!pairs.contains(&(":A".into(), ":C".into())));
}

#[test]
fn successive_deletion_base_survives_original_revision_eviction() {
    // Eight updates exceed incr_session's six-revision memo, so the original
    // source/index owner is evicted before the last two updates.
    const COMPONENTS: usize = 8;
    let source = |deleted: usize| {
        let mut text = String::from(HEADER);
        for i in 0..COMPONENTS {
            for tag in ["A", "B", "C"] {
                text.push_str(&format!("Declaration(Class(:{tag}{i}))\n"));
            }
        }
        for i in 0..COMPONENTS {
            text.push_str(&format!("SubClassOf(:A{i} :B{i})\n"));
            if i >= deleted {
                text.push_str(&format!("SubClassOf(:B{i} :C{i})\n"));
            }
        }
        text.push_str(")\n");
        text
    };
    let revisions: Vec<String> = (0..=COMPONENTS).map(source).collect();
    let rows = session(&revisions);
    assert_eq!(rows.len(), revisions.len());
    for (i, (row, revision)) in rows.iter().zip(&revisions).enumerate() {
        assert_eq!(row["status"], "ok", "revision {i}: {row:#?}");
        assert_eq!(canonical(&row["result"]), canonical(&fresh(revision, 120 + i)), "revision {i}");
        if i == 0 { continue; }
        let receipt = &row["receipt"];
        assert_eq!(receipt["strategy"], "module_reuse", "revision {i}");
        assert_eq!(receipt["base_revision_statements"], (5 * COMPONENTS - (i - 1)) as u64, "revision {i}");
        assert_eq!(receipt["removed_axioms"], 1, "revision {i}");
        assert_eq!(receipt["reclassified_subjects"], 2, "revision {i}");
        assert_eq!(receipt["module_axioms"], 1, "revision {i}");
        assert_eq!(receipt["index_axioms"], (2 * COMPONENTS) as u64, "revision {i}");
    }
}


#[test]
fn successive_nominal_assertion_and_tbox_deletions_keep_separate_index_masks() {
    // The two immutable indexes have different axiom spaces: six TBox axioms
    // versus eight assertion-keeping axioms. Exercise switching both ways
    // after the preceding deletion has become the current retained base.
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
    let no_assertion = ontology(&[base[0], base[1], base[2], base[3], base[4], base[5], base[6]]);
    let no_tbox = ontology(&[base[0], base[1], base[2], base[3], base[4], base[6], base[7]]);
    let both_deleted = ontology(&[base[0], base[1], base[2], base[3], base[4], base[6]]);
    for (order, first, strategies, index_sizes, removed_sizes) in [
        ("assertion-then-tbox", no_assertion,
         ["subject_reuse", "module_reuse"], [6_u64, 8], [1_u64, 1]),
        ("tbox-then-assertion", no_tbox,
         ["module_reuse", "subject_reuse"], [8_u64, 6], [1_u64, 1]),
    ] {
        let revisions = [original.clone(), first, both_deleted.clone()];
        let rows = session(&revisions);
        assert_eq!(rows.len(), revisions.len(), "{order}");
        for (i, (row, source)) in rows.iter().zip(&revisions).enumerate() {
            assert_eq!(row["status"], "ok", "{order}, revision {i}: {row:#?}");
            assert_eq!(canonical(&row["result"]), canonical(&fresh(source, 140 + i)),
                "{order}, revision {i}");
            if i == 0 { continue; }
            assert_eq!(row["receipt"]["strategy"], strategies[i - 1], "{order}, revision {i}");
            assert_eq!(row["receipt"]["index_axioms"], index_sizes[i - 1], "{order}, revision {i}");
            assert_eq!(row["receipt"]["removed_axioms"], removed_sizes[i - 1], "{order}, revision {i}");
        }
        let first_base = rows[1]["receipt"]["base_revision_statements"].as_u64().unwrap();
        assert_eq!(rows[2]["receipt"]["base_revision_statements"], first_base - 1,
            "{order}: second deletion must use the previous exact retained revision");
        let (_, _, prior_pairs) = canonical(&rows[1]["result"]);
        assert_eq!(prior_pairs.contains(&(":H".into(), ":G".into())), order == "assertion-then-tbox");
        let (_, _, pairs) = canonical(&rows[2]["result"]);
        assert!(!pairs.contains(&(":H".into(), ":G".into())),
            "{order}: removed F-to-G support must not survive the other index's mask");
    }
}


#[test]
fn independent_addition_and_mixed_edit_retain_published_rows() {
    let original = ontology(&["SubClassOf(:A :B)", "SubClassOf(:E :F)"]);
    for (case, changed, removed) in [
        ("addition", ontology(&["SubClassOf(:A :B)", "SubClassOf(:B :C)", "SubClassOf(:E :F)"]), 0_u64),
        ("mixed", ontology(&["SubClassOf(:A :C)", "SubClassOf(:E :F)"]), 1_u64),
    ] {
        let rows = session(&[original.clone(), changed.clone()]);
        assert_eq!(rows.len(), 2, "{case}");
        assert_eq!(rows[1]["status"], "ok", "{case}: {:#?}", rows[1]);
        assert_eq!(canonical(&rows[1]["result"]), canonical(&fresh(&changed, 160)), "{case}");
        let receipt = &rows[1]["receipt"];
        assert_eq!(receipt["strategy"], "common_module_reuse", "{case}: {receipt:#?}");
        assert_eq!(receipt["added_axioms"], 1, "{case}");
        assert_eq!(receipt["removed_axioms"], removed, "{case}");
        assert_eq!(receipt["statement_delta_verified"], true, "{case}");
        assert!(receipt["reused_subjects"].as_u64().unwrap() > 0, "{case}");
        assert!(receipt["reclassified_subjects"].as_u64().unwrap() > 0, "{case}");
        assert!(receipt["rebuilt_index_axioms"].as_u64().unwrap() > 0, "{case}");
        assert_eq!(receipt["reused_index_axioms"], 0, "{case}");
        assert_eq!(receipt["resumed_backend_states"], 0, "{case}");
        let (_, _, pairs) = canonical(&rows[1]["result"]);
        assert!(pairs.contains(&(":E".into(), ":F".into())), "{case}");
        assert!(pairs.contains(&(":A".into(), ":C".into())), "{case}");
        if case == "mixed" { assert!(!pairs.contains(&(":A".into(), ":B".into()))); }
    }
}

#[test]
fn public_class_kind_removal_and_reintroduction_use_current_source_domain() {
    let common = "Declaration(Class(:B))\nDeclaration(Class(:X))\nDeclaration(Class(:E))\nDeclaration(Class(:F))\nDeclaration(ObjectProperty(:A))\nSubClassOf(owl:Thing :B)\nSubClassOf(:E :F)\n";
    let original = format!("{HEADER}{common}Declaration(Class(:A))\nSubClassOf(:A :B)\nSubClassOf(:X :A)\n)\n");
    let removed = format!("{HEADER}{common})\n");
    // A still occurs as an object property in the middle revision. Restoring
    // only its Class declaration must nevertheless introduce a queried class.
    // Also introduce C so this revision is not a subset of the original
    // cached source; the test must exercise the common addition path.
    let restored = format!("{HEADER}{common}Declaration(Class(:A))\nDeclaration(Class(:C))\n)\n");
    let revisions = [original, removed, restored];
    let rows = session(&revisions);
    assert_eq!(rows.len(), 3);
    for (i, (row, source)) in rows.iter().zip(&revisions).enumerate() {
        assert_eq!(row["status"], "ok", "revision {i}: {row:#?}");
        assert_eq!(canonical(&row["result"]), canonical(&fresh(source, 170 + i)), "revision {i}");
    }
    let (_, _, removed_pairs) = canonical(&rows[1]["result"]);
    assert!(removed_pairs.iter().all(|(a, b)| a != ":A" && b != ":A"));
    let (_, _, restored_pairs) = canonical(&rows[2]["result"]);
    assert!(restored_pairs.contains(&(":A".into(), ":B".into())));
    assert!(!restored_pairs.contains(&(":X".into(), ":A".into())));
    assert_eq!(rows[2]["receipt"]["strategy"], "common_module_reuse");
}

#[test]
fn invalid_replacement_preserves_current_revision_and_answer() {
    let original = ontology(&["SubClassOf(:A :B)", "SubClassOf(:E :F)"]);
    let invalid = ontology(&["SubClassOf(:A :B)", "SubClassOf(:B :Undeclared)"]);
    let rows = session(&[original.clone(), invalid, original.clone()]);
    assert_eq!(rows.len(), 3);
    assert_eq!(rows[0]["status"], "ok");
    assert_eq!(rows[1]["status"], "error", "{:#?}", rows[1]);
    assert_eq!(rows[2]["status"], "ok");
    assert_eq!(rows[0]["revision"], 1);
    assert_eq!(rows[2]["revision"], 2);
    assert_eq!(rows[2]["receipt"]["strategy"], "exact_reuse");
    assert_eq!(rows[2]["receipt"]["added_statements"], 0);
    assert_eq!(rows[2]["receipt"]["removed_statements"], 0);
    assert_eq!(canonical(&rows[2]["result"]), canonical(&fresh(&original, 180)));
    assert_eq!(canonical(&rows[0]["result"]), canonical(&rows[2]["result"]));
}

#[test]
fn transaction_delta_uses_current_revision_when_analysis_uses_older_consistent_base() {
    let original = ontology(&["SubClassOf(:A :B)", "SubClassOf(:E :F)"]);
    let inconsistent = ontology(&["SubClassOf(:A :B)", "SubClassOf(:E :F)",
        "SubClassOf(owl:Thing owl:Nothing)"]);
    let changed = ontology(&["SubClassOf(:A :B)", "SubClassOf(:E :F)", "SubClassOf(:B :C)"]);
    let revisions = [original, inconsistent, changed];
    let rows = session(&revisions);
    assert_eq!(rows.len(), 3);
    for (i, (row, source)) in rows.iter().zip(&revisions).enumerate() {
        assert_eq!(row["status"], "ok", "revision {i}: {row:#?}");
        assert_eq!(canonical(&row["result"]), canonical(&fresh(source, 190 + i)), "revision {i}");
    }
    assert_eq!(rows[1]["result"]["consistent"], false);
    let receipt = &rows[2]["receipt"];
    assert_eq!(receipt["strategy"], "common_module_reuse", "{receipt:#?}");
    assert_eq!(receipt["statement_delta_verified"], true);
    // The selected consistent base has no removed axiom. The public transaction
    // does remove the current global contradiction, as well as adding B <= C.
    assert_eq!(receipt["added_axioms"], 1);
    assert_eq!(receipt["removed_axioms"], 1);
    assert_eq!(receipt["added_statements"], 1);
    assert_eq!(receipt["removed_statements"], 1);
    assert_eq!(receipt["base_revision_statements"], 13, "selected original: 11 declarations and two axioms");
    assert!(receipt["reused_subjects"].as_u64().unwrap() > 0);
    assert_eq!(receipt["resumed_backend_states"], 0);
}


#[test]
fn declined_common_module_reports_completed_preparation_in_full_fallback() {
    let original = ontology(&["SubClassOf(:A :B)", "SubClassOf(:E :F)"]);
    let global = ontology(&["SubClassOf(:A :B)", "SubClassOf(:E :F)", "SubClassOf(owl:Thing :D)"]);
    let rows = session(&[original, global.clone()]);
    assert_eq!(rows.len(), 2);
    assert_eq!(rows[1]["status"], "ok", "{:#?}", rows[1]);
    assert_eq!(canonical(&rows[1]["result"]), canonical(&fresh(&global, 200)));
    let receipt = &rows[1]["receipt"];
    assert_eq!(receipt["strategy"], "full_classify");
    assert_eq!(receipt["fallback_reason"], "changed axiom belongs to the union empty-signature module");
    // The initial base was already indexed. This transaction compiled the
    // NEW three-axiom theory; the addition union shares that same index.
    assert_eq!(receipt["index_build_calls"], 1);
    assert_eq!(receipt["index_build_failures"], 0);
    assert_eq!(receipt["rebuilt_index_axioms"], 3);
    assert_eq!(receipt["reused_index_axioms"], 0);
    assert_eq!(receipt["resumed_backend_states"], 0);
    assert_eq!(receipt["meaningful_incremental_update"], false);
}

#[test]
fn successful_common_module_counts_preparation_once_and_exact_reuse_builds_nothing() {
    let original = ontology(&["SubClassOf(:A :B)", "SubClassOf(:E :F)"]);
    let changed = ontology(&["SubClassOf(:A :B)", "SubClassOf(:E :F)", "SubClassOf(:B :C)"]);
    let rows = session(&[original, changed.clone(), changed.clone()]);
    assert_eq!(rows.len(), 3);
    for (index, row) in rows.iter().enumerate().skip(1) {
        assert_eq!(row["status"], "ok", "revision {index}: {row:#?}");
        assert_eq!(canonical(&row["result"]), canonical(&fresh(&changed, 210 + index)));
    }
    let receipt = &rows[1]["receipt"];
    assert_eq!(receipt["strategy"], "common_module_reuse");
    assert_eq!(receipt["index_build_calls"], 1);
    assert_eq!(receipt["index_build_failures"], 0);
    assert_eq!(receipt["rebuilt_index_axioms"], 3);
    assert_eq!(receipt["reused_index_axioms"], 0);
    assert!(receipt["reused_subjects"].as_u64().unwrap() > 0);
    let exact = &rows[2]["receipt"];
    assert_eq!(exact["strategy"], "exact_reuse");
    assert_eq!(exact["index_build_calls"], 0);
    assert_eq!(exact["index_build_failures"], 0);
    assert_eq!(exact["rebuilt_index_axioms"], 0);
}


#[test]
fn full_fallback_preserves_cross_revision_compiler_donor_without_claiming_same_call_reuse() {
    let original = ontology(&["SubClassOf(:A :B)", "SubClassOf(:E :F)"]);
    let first = ontology(&["SubClassOf(:A :B)", "SubClassOf(:E :F)", "SubClassOf(owl:Thing :D)"]);
    let second = ontology(&["SubClassOf(:A :B)", "SubClassOf(:E :F)", "SubClassOf(owl:Thing :G)"]);
    let revisions = [original, first, second];
    let rows = session(&revisions);
    assert_eq!(rows.len(), 3);
    for (i, (row, source)) in rows.iter().zip(&revisions).enumerate() {
        assert_eq!(row["status"], "ok", "revision {i}: {row:#?}");
        assert_eq!(canonical(&row["result"]), canonical(&fresh(source, 220 + i)));
    }
    let first = &rows[1]["receipt"];
    assert_eq!(first["strategy"], "full_classify");
    assert_eq!(first["cross_revision_compiled_axioms"], 0);
    assert_eq!(first["same_update_compiled_axioms"], 0);
    assert_eq!(first["meaningful_incremental_update"], false);
    let second = &rows[2]["receipt"];
    assert_eq!(second["strategy"], "full_classify");
    assert_eq!(second["cross_revision_compiled_axioms"], 3);
    assert_eq!(second["same_update_compiled_axioms"], 3);
    assert_eq!(second["compiled_locality_axioms"], 1);
    assert_eq!(second["csr_axiom_records"], 7);
    assert_eq!(second["reused_subjects"], 0);
    assert_eq!(second["reused_index_axioms"], 0);
    assert_eq!(second["resumed_backend_states"], 0);
    assert_eq!(second["meaningful_incremental_update"], true);
}


#[test]
fn positive_abox_mixed_edits_retain_rows_then_negative_constraints_decline_projection() {
    let original = ontology(&["SubClassOf(:A :B)", "SubClassOf(:E :F)",
        "ClassAssertion(:A _:x)", "ClassAssertion(:E _:y)"]);
    let mixed = ontology(&["SubClassOf(:A :B)", "SubClassOf(:B :C)",
        "SubClassOf(:E :F)", "ClassAssertion(:E _:y)"]);
    let inconsistent = ontology(&["SubClassOf(:A :B)", "SubClassOf(:B :C)",
        "SubClassOf(:E :F)", "ClassAssertion(:E _:y)", "DisjointClasses(:E :F)"]);
    let revisions = [original, mixed, inconsistent];
    let rows = session(&revisions);
    assert_eq!(rows.len(), 3);
    for (index, (row, source)) in rows.iter().zip(&revisions).enumerate() {
        assert_eq!(row["status"], "ok", "revision {index}: {row:#?}");
        assert_eq!(canonical(&row["result"]), canonical(&fresh(source, 230 + index)));
    }
    let receipt = &rows[1]["receipt"];
    assert_eq!(receipt["strategy"], "positive_abox_module_reuse", "{receipt:#?}");
    assert_eq!(receipt["added_axioms"], 1);
    assert_eq!(receipt["removed_axioms"], 1);
    assert!(receipt["reused_subjects"].as_u64().unwrap() > 0);
    assert!(receipt["reclassified_subjects"].as_u64().unwrap() > 0);
    assert_eq!(receipt["module_axioms"], 2);
    assert_eq!(receipt["resumed_backend_states"], 0);
    let (_, _, pairs) = canonical(&rows[1]["result"]);
    assert!(pairs.contains(&(":A".into(), ":C".into())));
    assert!(pairs.contains(&(":E".into(), ":F".into())));
    // Independent semantic expectation: the still-present E assertion clashes
    // with E <= F and E disjoint F. Analysis-only assertion masks must not leak.
    assert_eq!(rows[2]["result"]["consistent"], false);
    assert_ne!(rows[2]["receipt"]["strategy"], "positive_abox_module_reuse");
}

#[test]
fn retained_inconsistency_support_survives_successive_mixed_edits_and_core_removal() {
    // All declarations remain stable, while every revision replaces an
    // unrelated logical axiom. No whole earlier source is a later subset.
    // Nine inconsistent revisions exceed MEMO_LIMIT and evict the original.
    let declarations = (0..9).map(|i| format!("Declaration(Class(:Transient{i}))\n")).collect::<String>();
    let mut revisions = Vec::new();
    for i in 0..9 {
        let unrelated = format!("SubClassOf(:Transient{i} :D)");
        revisions.push(ontology(&[&declarations, "SubClassOf(owl:Thing owl:Nothing)", &unrelated]));
    }
    revisions.push(ontology(&[&declarations, "SubClassOf(:Transient8 :D)"]));
    let rows = session(&revisions);
    assert_eq!(rows.len(), revisions.len());
    for (i, (row, source)) in rows.iter().zip(&revisions).enumerate() {
        assert_eq!(row["status"], "ok", "revision {i}: {row:#?}");
        assert_eq!(canonical(&row["result"]), canonical(&fresh(source, 240 + i)), "revision {i}");
        assert_eq!(row["result"]["consistent"], i == 9);
        if (1..9).contains(&i) {
            let receipt = &row["receipt"];
            assert_eq!(receipt["strategy"], "inconsistency_witness_reuse", "revision {i}: {receipt:#?}");
            assert_eq!(receipt["reused_complete_answer"], true);
            assert_eq!(receipt["resumed_backend_states"], 0);
            assert_eq!(receipt["index_build_calls"], 0);
            assert_eq!(receipt["added_axioms"], 1);
            assert_eq!(receipt["removed_axioms"], 1);
        }
    }
    assert_eq!(rows[9]["receipt"]["strategy"], "full_classify");
    assert_eq!(rows[9]["receipt"]["reused_complete_answer"], false);
}

#[test]
fn retained_inconsistency_rejects_invalid_addition_without_committing_revision() {
    let clash = "SubClassOf(owl:Thing owl:Nothing)";
    let original = ontology(&[clash, "SubClassOf(:E :F)"]);
    let invalid = ontology(&[clash, "SubClassOf(:E :F)", "SubClassOf(:A :Undeclared)"]);
    let replacement = ontology(&[clash, "SubClassOf(:E :G)"]);
    let rows = session(&[original.clone(), invalid, replacement.clone()]);
    assert_eq!(rows.len(), 3);
    assert_eq!(rows[0]["status"], "ok");
    assert_eq!(rows[1]["status"], "error", "{:#?}", rows[1]);
    assert_eq!(rows[2]["status"], "ok");
    assert_eq!(rows[0]["revision"], 1);
    assert_eq!(rows[2]["revision"], 2);
    assert_eq!(rows[2]["receipt"]["strategy"], "inconsistency_witness_reuse");
    assert_eq!(rows[2]["receipt"]["added_axioms"], 1);
    assert_eq!(rows[2]["receipt"]["removed_axioms"], 1);
    assert_eq!(rows[2]["result"]["consistent"], false);
    assert_eq!(canonical(&rows[0]["result"]), canonical(&fresh(&original, 260)));
    assert_eq!(canonical(&rows[2]["result"]), canonical(&fresh(&replacement, 261)));
}

#[test]
fn pure_addition_shares_one_new_index_while_mixed_edit_keeps_explicit_union() {
    let original = ontology(&["SubClassOf(:A :B)", "SubClassOf(:E :F)"]);
    let added = ontology(&["SubClassOf(:E :F)", "SubClassOf(:B :C)",
        "SubClassOf(:A :B)", "SubClassOf(:A :B)"]);
    let mixed = ontology(&["SubClassOf(:E :F)", "SubClassOf(:B :G)",
        "SubClassOf(:A :B)", "SubClassOf(:A :B)"]);
    let revisions = [original, added, mixed];
    let rows = session(&revisions);
    for (i, (row, source)) in rows.iter().zip(&revisions).enumerate() {
        assert_eq!(row["status"], "ok", "revision {i}: {row:#?}");
        assert_eq!(canonical(&row["result"]), canonical(&fresh(source, 270 + i)), "revision {i}");
    }
    let added = &rows[1]["receipt"];
    assert_eq!(added["strategy"], "common_module_reuse");
    assert_eq!(added["index_build_calls"], 1);
    assert_eq!(added["rebuilt_index_axioms"], 3);
    assert_eq!(added["csr_axiom_records"], 3);
    assert_eq!(added["same_update_compiled_axioms"], 0);
    assert_eq!(added["resumed_backend_states"], 0);
    assert!(added["reused_subjects"].as_u64().unwrap() > 0);
    let mixed = &rows[2]["receipt"];
    assert_eq!(mixed["strategy"], "common_module_reuse");
    assert_eq!(mixed["index_build_calls"], 1);
    assert_eq!(mixed["csr_axiom_records"], 4);
    assert_eq!(mixed["same_update_compiled_axioms"], 0);
    assert_eq!(mixed["resumed_backend_states"], 0);
    let (_, _, pairs) = canonical(&rows[2]["result"]);
    assert!(pairs.contains(&(":A".into(), ":G".into())));
    assert!(!pairs.contains(&(":A".into(), ":C".into())));
}

#[test]
fn mixed_reintroduction_uses_enabled_old_donor_not_historical_union_membership() {
    let original = ontology(&["SubClassOf(:A :B)", "SubClassOf(:B :C)",
        "SubClassOf(:E :F)", "SubClassOf(:F :G)"]);
    let masked = ontology(&["SubClassOf(:A :B)", "SubClassOf(:B :G)",
        "SubClassOf(:E :F)", "SubClassOf(:F :G)"]);
    // B<=C is physically present but disabled in the saved union. G<=H is
    // novel, so this source cannot take exact restoration of the first memo.
    let reintroduced = ontology(&["SubClassOf(:A :B)", "SubClassOf(:B :C)",
        "SubClassOf(:E :F)", "SubClassOf(:F :G)", "SubClassOf(:G :H)"]);
    let revisions = [original, masked, reintroduced];
    let rows = session(&revisions);
    assert_eq!(rows.len(), revisions.len());
    for (i, (row, source)) in rows.iter().zip(&revisions).enumerate() {
        assert_eq!(row["status"], "ok", "revision {i}: {row:#?}");
        assert_eq!(canonical(&row["result"]), canonical(&fresh(source, 280 + i)), "revision {i}");
    }
    let receipt = &rows[2]["receipt"];
    assert_eq!(receipt["strategy"], "common_module_reuse");
    assert_eq!(receipt["index_build_calls"], 1);
    assert_eq!(receipt["csr_axiom_records"], 6);
    assert_eq!(receipt["cross_revision_compiled_axioms"], 4);
    assert_eq!(receipt["compiled_locality_axioms"], 2);
    assert_eq!(receipt["same_update_compiled_axioms"], 0);
    assert_eq!(receipt["resumed_backend_states"], 0);
    let (_, _, pairs) = canonical(&rows[2]["result"]);
    assert!(pairs.contains(&(":A".into(), ":C".into())));
    assert!(pairs.contains(&(":E".into(), ":H".into())));
    assert!(!pairs.contains(&(":A".into(), ":G".into())));
}
#[test]
fn declined_mixed_union_keeps_exact_new_full_index_for_nominal_deletion() {
    let shared = [
        "EquivalentClasses(:C ObjectOneOf(:a))",
        "SubClassOf(:C :D)",
        "ClassAssertion(:C :a)",
        "SubClassOf(:A :B)",
    ];
    // The tautology is semantically Thing but uses only ordinary class names.
    // Both changed GCIs are non-local even at the empty signature, so common
    // publication must decline. The nominal prevents positive-ABox projection.
    let old_global = "SubClassOf(ObjectUnionOf(:E ObjectComplementOf(:E)) :G)";
    let new_global = "SubClassOf(ObjectUnionOf(:E ObjectComplementOf(:E)) :H)";
    let original = ontology(&[shared[0], shared[1], shared[2], shared[3], old_global]);
    let changed = ontology(&[shared[0], shared[1], shared[2], shared[3], new_global]);
    let deleted = ontology(&[shared[0], shared[1], shared[2], new_global]);
    let revisions = [original, changed, deleted];
    let rows = session(&revisions);
    assert_eq!(rows.len(), revisions.len());
    for (i, (row, source)) in rows.iter().zip(&revisions).enumerate() {
        assert_eq!(row["status"], "ok", "revision {i}: {row:#?}");
        assert_eq!(row["result"]["consistent"], true, "revision {i}");
        assert_eq!(row["result"]["dropped"], 0, "revision {i}");
        assert_eq!(canonical(&row["result"]), canonical(&fresh(source, 300 + i)),
            "revision {i}");
    }
    let old_pairs = canonical(&rows[0]["result"]).2;
    let changed_pairs = canonical(&rows[1]["result"]).2;
    let deleted_pairs = canonical(&rows[2]["result"]).2;
    assert!(old_pairs.contains(&(":A".into(), ":G".into())));
    assert!(!changed_pairs.contains(&(":A".into(), ":G".into())),
        "the removed OLD global axiom must not survive fallback");
    assert!(changed_pairs.contains(&(":A".into(), ":H".into())));
    assert!(changed_pairs.contains(&(":A".into(), ":B".into())));
    assert!(!deleted_pairs.contains(&(":A".into(), ":B".into())));
    assert!(!deleted_pairs.contains(&(":A".into(), ":G".into())));
    assert!(deleted_pairs.contains(&(":A".into(), ":H".into())));
    assert!(deleted_pairs.contains(&(":C".into(), ":D".into())));

    let fallback = &rows[1]["receipt"];
    assert_eq!(fallback["strategy"], "full_classify", "{fallback:#?}");
    assert_eq!(fallback["fallback_reason"], "changed axiom belongs to the union empty-signature module");
    assert_eq!(fallback["added_axioms"], 1);
    assert_eq!(fallback["removed_axioms"], 1);
    // Initial OLD has its nominal TBox/full pair ready. This transaction
    // assembles the six-axiom union, then exact five-axiom NEW after fallback.
    assert_eq!(fallback["index_build_calls"], 2);
    assert_eq!(fallback["index_build_failures"], 0);
    assert_eq!(fallback["csr_axiom_records"], 11);
    assert_eq!(fallback["cross_revision_compiled_axioms"], 5);
    assert_eq!(fallback["same_update_compiled_axioms"], 5);
    assert_eq!(fallback["compiled_locality_axioms"], 1);
    assert_eq!(fallback["reused_subjects"], 0);
    assert_eq!(fallback["resumed_backend_states"], 0);
    assert_eq!(fallback["meaningful_incremental_update"], true,
        "only actual cross-revision compiler work justifies meaningful here");

    let deletion = &rows[2]["receipt"];
    assert_eq!(deletion["strategy"], "module_reuse", "{deletion:#?}");
    // The cached exact NEW full index has five axioms. Its TBox has four;
    // a stale OLD-union full index would have six. Thus this checks the
    // production BaseState.index -> compiler_full substitution, not only parity.
    assert_eq!(deletion["index_axioms"], 5, "{deletion:#?}");
    assert_eq!(deletion["base_revision_statements"], 16,
        "closest fallback NEW: eleven declarations plus five axioms");
    assert_eq!(deletion["added_axioms"], 0);
    assert_eq!(deletion["removed_axioms"], 1);
    assert!(deletion["reclassified_subjects"].as_u64().unwrap() > 0);
    assert!(deletion["reused_subjects"].as_u64().unwrap() > 0);
    assert_eq!(deletion["resumed_backend_states"], 0);
    assert_eq!(deletion["meaningful_incremental_update"], true);
}

#[test]
fn changed_outer_grammar_is_rejected_without_committing_deletion_or_content_memo() {
    let base = "Prefix(:=<urn:gap:>) Ontology(Declaration(Class(:A)) Declaration(Class(:B)) SubClassOf(:A :B))";
    // Exact root reproduction: source statements are a valid subset, but VT
    // belongs to locality's old byte whitespace table, not the OWL grammar.
    let bad_delete = "Prefix(:=<urn:gap:>) Ontology(Declaration(Class(:A)) \u{000b}Declaration(Class(:B)))";
    // The same invalid gap must not hit order-independent content memo reuse.
    let bad_same_content = base.replace(" Declaration(Class(:B))", " \u{000b}Declaration(Class(:B))");
    let path = std::env::temp_dir().join(format!("km-gap-refusal-{}.ofn", std::process::id()));
    for text in [bad_delete, bad_same_content.as_str()] {
        std::fs::write(&path,text).unwrap();
        let output=Command::new(env!("CARGO_BIN_EXE_km")).arg("classify").arg(&path).output().unwrap();
        assert!(!output.status.success(),"fresh accepted malformed outer grammar");
        assert!(String::from_utf8_lossy(&output.stderr).contains("invalid OWL 2"));
    }
    let _=std::fs::remove_file(path);
    let mut child=Command::new(env!("CARGO_BIN_EXE_km")).arg("incremental-source")
        .stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::piped()).spawn().unwrap();
    for request in [serde_json::json!({"op":"init","functional_syntax":base}),
                    serde_json::json!({"op":"replace","functional_syntax":bad_delete}),
                    serde_json::json!({"op":"classify"}),
                    serde_json::json!({"op":"replace","functional_syntax":bad_same_content}),
                    serde_json::json!({"op":"classify"})] {
        serde_json::to_writer(child.stdin.as_mut().unwrap(),&request).unwrap();
        child.stdin.as_mut().unwrap().write_all(b"\n").unwrap();
    }
    drop(child.stdin.take());let output=child.wait_with_output().unwrap();assert!(output.status.success());
    let rows:Vec<serde_json::Value>=String::from_utf8(output.stdout).unwrap().lines().map(|s|serde_json::from_str(s).unwrap()).collect();
    assert_eq!(rows.len(),5);assert_eq!(rows[0]["status"],"ok");
    for i in [1,3] {assert_eq!(rows[i]["status"],"error");}
    for i in [2,4] {assert_eq!(rows[i]["status"],"ok");assert_eq!(rows[i]["revision"],1);assert_eq!(canonical(&rows[i]["result"]),canonical(&rows[0]["result"]));}
}

#[test]
fn named_subclass_validation_origin_survives_deletion_and_checks_common_revision() {
    let original=ontology(&["SubClassOf(:A :B)","DisjointClasses(:B :C)","SubClassOf(:E :F)"]);
    let deleted=ontology(&["SubClassOf(:E :F)"]);
    let added=ontology(&["SubClassOf(:A :C)","SubClassOf(:E :F)"]);
    let invalid=ontology(&["SubClassOf(:A :Undeclared)","SubClassOf(:E :F)"]);
    let mut child=Command::new(env!("CARGO_BIN_EXE_km")).arg("incremental-source")
        .env("KM_CACHE_CONFORMANCE","1").env("KM_INCR_TIMING","1")
        .stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::piped()).spawn().unwrap();
    for request in [serde_json::json!({"op":"init","functional_syntax":original}),
                    serde_json::json!({"op":"replace","functional_syntax":deleted}),
                    serde_json::json!({"op":"replace","functional_syntax":added}),
                    serde_json::json!({"op":"replace","functional_syntax":invalid}),
                    serde_json::json!({"op":"classify"})] {
        serde_json::to_writer(child.stdin.as_mut().unwrap(),&request).unwrap();
        child.stdin.as_mut().unwrap().write_all(b"\n").unwrap();
    }
    drop(child.stdin.take());let output=child.wait_with_output().unwrap();assert!(output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("KM_INCR_TIMING common source validation certificate"),"{}",String::from_utf8_lossy(&output.stderr));
    let rows:Vec<serde_json::Value>=String::from_utf8(output.stdout).unwrap().lines().map(|s|serde_json::from_str(s).unwrap()).collect();
    assert_eq!(rows.len(),5);
    for (i,text) in [&original,&deleted,&added].iter().enumerate() {assert_eq!(rows[i]["status"],"ok");assert_eq!(canonical(&rows[i]["result"]),canonical(&fresh(text,500+i)));}
    assert_eq!(rows[1]["receipt"]["strategy"],"module_reuse");
    assert_eq!(rows[2]["receipt"]["strategy"],"common_module_reuse");
    assert_eq!(rows[3]["status"],"error");assert_eq!(rows[4]["status"],"ok");assert_eq!(rows[4]["revision"],3);
    assert_eq!(canonical(&rows[4]["result"]),canonical(&rows[2]["result"]));
}
