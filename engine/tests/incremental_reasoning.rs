use std::io::Cursor;

use kobayashi_marust::elcomplete::{self, ElResult};
use kobayashi_marust::incremental::{run_jsonl_session, IncrementalElClassifier, IncrementalError};
use kobayashi_marust::json_io::JClause;

fn clauses(json: &str) -> Vec<JClause> {
    serde_json::from_str(json).expect("test clause JSON")
}

fn v(name: &str) -> String {
    format!(r#"{{"kind":"var","name":"{name}"}}"#)
}

fn concept(name: &str, var: &str) -> String {
    format!(
        r#"{{"kind":"concept","concept":"{name}","term":{}}}"#,
        v(var)
    )
}

fn role(name: &str, source: &str, target: &str) -> String {
    format!(
        r#"{{"kind":"role","role":"{name}","source":{},"target":{}}}"#,
        v(source),
        v(target)
    )
}

fn role_fun(name: &str, source: &str, function: &str) -> String {
    format!(
        r#"{{"kind":"role","role":"{name}","source":{},"target":{{"kind":"fun","function":"{function}","arg":{}}}}}"#,
        v(source),
        v(source)
    )
}

fn concept_fun(name: &str, function: &str, var: &str) -> String {
    format!(
        r#"{{"kind":"concept","concept":"{name}","term":{{"kind":"fun","function":"{function}","arg":{}}}}}"#,
        v(var)
    )
}

fn clause(body: &[String], head: &[String]) -> String {
    format!(
        r#"{{"body":[{}],"head":[{}]}}"#,
        body.join(","),
        head.join(",")
    )
}

fn normalise(mut result: ElResult) -> ElResult {
    for supers in result.subsumptions.values_mut() {
        supers.sort_unstable();
    }
    result
}

#[test]
fn addition_reuses_fixpoint_and_matches_fresh_completion() {
    let initial = clauses(&format!(
        "[{}]",
        clause(&[concept("A", "x")], &[concept("B", "x")])
    ));
    let addition = clauses(&format!(
        "[{}]",
        clause(&[concept("B", "x")], &[concept("C", "x")])
    ));

    let mut incremental = IncrementalElClassifier::new(initial.clone()).expect("pure EL++");
    assert_eq!(incremental.is_subsumed_by("A", "C"), Some(false));
    let update = incremental
        .add_clauses(addition.clone())
        .expect("supported addition");
    assert_eq!(update.revision, 1);
    assert!(update.reused_subsumptions > 0);
    assert!(update.new_subsumptions > 0);
    assert_eq!(incremental.is_subsumed_by("A", "C"), Some(true));

    let mut union = initial;
    union.extend(addition);
    let fresh = elcomplete::classify(union).expect("fresh EL++ completion");
    assert_eq!(incremental.result(), normalise(fresh));
}

#[test]
fn role_hierarchy_addition_replays_existing_edges() {
    // Initial: A ⊑ ∃R.B and ∃S.B ⊑ D. Adding R ⊑ S must lift the
    // already-materialised R edge and fire the existing NF4 rule.
    let initial = clauses(&format!(
        "[{},{},{}]",
        clause(&[concept("A", "x")], &[role_fun("R", "x", "f")]),
        clause(&[concept("A", "x")], &[concept_fun("B", "f", "x")]),
        clause(
            &[role("S", "x", "y"), concept("B", "y")],
            &[concept("D", "x")]
        ),
    ));
    let addition = clauses(&format!(
        "[{}]",
        clause(&[role("R", "x", "y")], &[role("S", "x", "y")])
    ));
    let mut incremental = IncrementalElClassifier::new(initial).expect("pure EL++");
    assert_eq!(incremental.is_subsumed_by("A", "D"), Some(false));
    let update = incremental.add_clauses(addition).expect("role inclusion");
    assert!(update.reused_edges > 0);
    assert!(update.new_edges > 0);
    assert_eq!(incremental.is_subsumed_by("A", "D"), Some(true));
}

#[test]
fn chain_conjunction_and_bottom_additions_close_from_old_facts() {
    let initial = clauses(&format!(
        "[{},{},{},{},{}]",
        clause(&[concept("A", "x")], &[role_fun("R", "x", "f")]),
        clause(&[concept("A", "x")], &[concept_fun("B", "f", "x")]),
        clause(&[concept("B", "x")], &[role_fun("S", "x", "g")]),
        clause(&[concept("B", "x")], &[concept_fun("C", "g", "x")]),
        clause(&[concept("A", "x")], &[concept("E", "x")]),
    ));
    let addition = clauses(&format!(
        "[{},{},{},{}]",
        clause(
            &[role("R", "x", "y"), role("S", "y", "z")],
            &[role("T", "x", "z")]
        ),
        clause(
            &[role("T", "x", "y"), concept("C", "y")],
            &[concept("D", "x")]
        ),
        clause(
            &[concept("D", "x"), concept("E", "x")],
            &[concept("F", "x")]
        ),
        clause(&[concept("F", "x")], &[]),
    ));
    let mut incremental = IncrementalElClassifier::new(initial.clone()).expect("pure EL++");
    assert_eq!(incremental.is_subsumed_by("A", "F"), Some(false));
    let update = incremental
        .add_clauses(addition.clone())
        .expect("NF2/NF4/NF5/NF7 addition");
    assert!(update.reused_fixpoint);
    assert_eq!(incremental.is_subsumed_by("A", "D"), Some(true));
    assert_eq!(incremental.is_subsumed_by("A", "F"), Some(true));
    assert_eq!(incremental.is_subsumed_by("A", "owl:Nothing"), Some(true));

    let mut union = initial;
    union.extend(addition);
    let fresh = elcomplete::classify(union).expect("fresh EL++ completion");
    assert_eq!(incremental.result(), normalise(fresh));
}

#[test]
fn reflexive_role_addition_seeds_existing_concept_nodes() {
    let initial = clauses(&format!(
        "[{},{}]",
        clause(&[concept("A", "x")], &[concept("B", "x")]),
        clause(
            &[role("R", "x", "y"), concept("B", "y")],
            &[concept("C", "x")]
        ),
    ));
    let addition = clauses(&format!("[{}]", clause(&[], &[role("R", "x", "x")])));
    let mut incremental = IncrementalElClassifier::new(initial).expect("pure EL++");
    assert_eq!(incremental.is_subsumed_by("A", "C"), Some(false));
    incremental
        .add_clauses(addition)
        .expect("reflexive role addition");
    assert_eq!(incremental.is_subsumed_by("A", "C"), Some(true));
}

#[test]
fn query_observes_explosion_for_an_inconsistent_snapshot() {
    let snapshot = clauses(&format!(
        "[{},{},{}]",
        clause(&[], &[concept("A", "x")]),
        clause(&[concept("A", "x")], &[]),
        clause(&[concept("B", "x")], &[concept("B", "x")]),
    ));
    let incremental = IncrementalElClassifier::new(snapshot).expect("pure inconsistent EL++");
    assert!(incremental.is_inconsistent());
    assert_eq!(
        incremental.is_subsumed_by("B", "not-in-signature"),
        Some(true)
    );
}

#[test]
fn rejected_non_el_addition_is_atomic() {
    let initial = clauses(&format!(
        "[{}]",
        clause(&[concept("A", "x")], &[concept("B", "x")])
    ));
    let non_el = clauses(&format!(
        "[{}]",
        clause(
            &[concept("A", "x")],
            &[concept("X", "x"), concept("Y", "x")]
        )
    ));
    let mut incremental = IncrementalElClassifier::new(initial).expect("pure EL++");
    let before = incremental.result();
    let error = incremental
        .add_clauses(non_el)
        .expect_err("disjunction is outside incremental EL++");
    assert_eq!(error, IncrementalError::NonElResidual { clauses: 1 });
    assert_eq!(incremental.revision(), 0);
    assert_eq!(incremental.clause_count(), 1);
    assert_eq!(incremental.result(), before);
}

#[test]
fn late_existential_filler_uses_safe_fresh_completion() {
    // A role half alone is interpreted by the batch EL route as A ⊑ ∃R.⊤.
    // Adding its B(f(x)) half changes that compact NF3 to A ⊑ ∃R.B, so the
    // session must not retain the old canonical TOP edge.
    let initial = clauses(&format!(
        "[{}]",
        clause(&[concept("A", "x")], &[role_fun("R", "x", "f")])
    ));
    let addition = clauses(&format!(
        "[{}]",
        clause(&[concept("A", "x")], &[concept_fun("B", "f", "x")])
    ));
    let mut incremental = IncrementalElClassifier::new(initial.clone()).expect("role half");
    let update = incremental
        .add_clauses(addition.clone())
        .expect("completed existential");
    assert!(!update.reused_fixpoint);
    assert_eq!(update.reused_subsumptions, 0);
    assert_eq!(update.reused_edges, 0);

    let mut union = initial;
    union.extend(addition);
    let fresh = elcomplete::classify(union).expect("fresh EL++ completion");
    assert_eq!(incremental.result(), normalise(fresh));
}

#[test]
fn jsonl_protocol_keeps_session_after_rejected_transaction() {
    let initial = clauses(&format!(
        "[{}]",
        clause(&[concept("A", "x")], &[concept("B", "x")])
    ));
    let unsupported = clauses(
        r#"[{"body":[],"head":[{"kind":"concept","concept":"X","term":{"kind":"aux","root":"r","label":[]}}]}]"#,
    );
    let addition = clauses(&format!(
        "[{}]",
        clause(&[concept("B", "x")], &[concept("C", "x")])
    ));
    let commands = [
        serde_json::json!({"op": "init", "clauses": initial}),
        serde_json::json!({"op": "add", "clauses": unsupported}),
        serde_json::json!({"op": "add", "clauses": addition}),
        serde_json::json!({"op": "is_subsumed_by", "sub": "A", "sup": "C"}),
    ]
    .into_iter()
    .map(|value| serde_json::to_string(&value).unwrap())
    .collect::<Vec<_>>()
    .join("\n");
    let mut output = Vec::new();
    run_jsonl_session(Cursor::new(commands), &mut output).expect("JSONL session");
    let rows: Vec<serde_json::Value> = String::from_utf8(output)
        .unwrap()
        .lines()
        .map(|line| serde_json::from_str(line).unwrap())
        .collect();
    assert_eq!(rows.len(), 4);
    assert_eq!(rows[1]["status"], "error");
    assert_eq!(rows[2]["update"]["revision"], 1);
    assert_eq!(rows[3]["entailed"], true);
}

#[test]
fn jsonl_protocol_transitions_to_cb_and_removes_by_stable_id() {
    std::env::set_var("KM_THREADS", "1");
    let initial = clauses(&format!(
        "[{}]",
        clause(&[concept("A", "x")], &[concept("B", "x")])
    ));
    let disjunction = clauses(&format!(
        "[{}]",
        clause(
            &[concept("A", "x")],
            &[concept("X", "x"), concept("Y", "x")]
        )
    ));
    let replacement = clauses(&format!(
        "[{}]",
        clause(&[concept("B", "x")], &[concept("C", "x")])
    ));
    let commands = [
        serde_json::json!({"op": "init", "clauses": initial}),
        serde_json::json!({"op": "add", "clauses": disjunction}),
        serde_json::json!({"op": "remove", "clause_ids": [2]}),
        serde_json::json!({
            "op": "change",
            "remove_clause_ids": [1],
            "add_clauses": replacement,
        }),
        serde_json::json!({"op": "stats"}),
    ]
    .into_iter()
    .map(|value| serde_json::to_string(&value).unwrap())
    .collect::<Vec<_>>()
    .join("\n");
    let mut output = Vec::new();
    run_jsonl_session(Cursor::new(commands), &mut output).expect("JSONL session");
    let rows: Vec<serde_json::Value> = String::from_utf8(output)
        .unwrap()
        .lines()
        .map(|line| serde_json::from_str(line).unwrap())
        .collect();
    assert_eq!(rows.len(), 5);
    assert_eq!(rows[0]["backend"], "el");
    assert_eq!(rows[0]["clause_ids"], serde_json::json!([1]));
    assert_eq!(rows[1]["update"]["backend_after"], "cb");
    assert_eq!(rows[1]["update"]["strategy"], "exact_rebuild");
    assert_eq!(
        rows[1]["update"]["added_clause_ids"],
        serde_json::json!([2])
    );
    assert_eq!(rows[2]["update"]["backend_after"], "el");
    assert_eq!(
        rows[2]["update"]["removed_clause_ids"],
        serde_json::json!([2])
    );
    assert_eq!(rows[3]["op"], "change");
    assert_eq!(rows[3]["update"]["revision"], 3);
    assert_eq!(
        rows[3]["update"]["removed_clause_ids"],
        serde_json::json!([1])
    );
    assert_eq!(
        rows[3]["update"]["added_clause_ids"],
        serde_json::json!([3])
    );
    assert_eq!(rows[4]["revision"], 3);
    assert_eq!(rows[4]["clause_ids"], serde_json::json!([3]));
}

#[test]
fn jsonl_protocol_reports_retained_cb_delta() {
    std::env::set_var("KM_THREADS", "1");
    let initial = clauses(&format!(
        "[{disjunction},{trigger}]",
        disjunction = clause(
            &[concept("A", "x")],
            &[concept("B", "x"), concept("C", "x")]
        ),
        trigger = clause(&[concept("B", "x")], &[concept("SeenB", "x")]),
    ));
    let addition = clauses(&format!(
        "[{}]",
        clause(&[concept("B", "x")], &[concept("D", "x")])
    ));
    let commands = [
        serde_json::json!({"op": "init", "clauses": initial}),
        serde_json::json!({"op": "add", "clauses": addition}),
    ]
    .into_iter()
    .map(|value| serde_json::to_string(&value).unwrap())
    .collect::<Vec<_>>()
    .join("\n");
    let mut output = Vec::new();
    run_jsonl_session(Cursor::new(commands), &mut output).expect("JSONL session");
    let rows: Vec<serde_json::Value> = String::from_utf8(output)
        .unwrap()
        .lines()
        .map(|line| serde_json::from_str(line).unwrap())
        .collect();
    assert_eq!(rows[0]["backend"], "cb");
    assert_eq!(rows[1]["update"]["strategy"], "cb_delta");
    assert_eq!(rows[1]["update"]["reused_fixpoint"], true);
}

#[test]
fn jsonl_protocol_rejects_unconsumed_side_channels() {
    let commands = [
        r#"{"op":"init","clauses":[],"rbox":[]}"#,
        r#"{"op":"stats"}"#,
    ]
    .join("\n");
    let mut output = Vec::new();
    run_jsonl_session(Cursor::new(commands), &mut output).expect("JSONL session");
    let rows: Vec<serde_json::Value> = String::from_utf8(output)
        .unwrap()
        .lines()
        .map(|line| serde_json::from_str(line).unwrap())
        .collect();
    assert_eq!(rows.len(), 2);
    assert_eq!(rows[0]["status"], "error");
    assert_eq!(rows[0]["op"], "parse");
    assert_eq!(rows[1]["status"], "error");
    assert_eq!(rows[1]["op"], "stats");
}
