use std::io::Write;
use std::process::{Command, Stdio};
use std::sync::Mutex;

use kobayashi_marust::incremental::{
    classify_cb_fresh, classify_ht_fresh, ChangeStrategy, IncrementalBackend,
    IncrementalClassifier, IncrementalReasoningError,
};
use kobayashi_marust::json_io::{JAtom, JClause, JTerm};

static ENV_LOCK: Mutex<()> = Mutex::new(());

fn env_lock() -> std::sync::MutexGuard<'static, ()> {
    ENV_LOCK
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
}

fn var(name: &str) -> JTerm {
    JTerm::Var {
        name: name.to_string(),
    }
}

fn ind(name: &str) -> JTerm {
    JTerm::Ind {
        name: name.to_string(),
    }
}

fn fun(name: &str) -> JTerm {
    JTerm::Fun {
        function: name.to_string(),
        arg: Box::new(var("x")),
    }
}

fn concept(name: &str, term: JTerm) -> JAtom {
    JAtom::Concept {
        concept: name.to_string(),
        term,
    }
}

fn role(name: &str, source: JTerm, target: JTerm) -> JAtom {
    JAtom::Role {
        role: name.to_string(),
        source,
        target,
    }
}

fn clause(body: Vec<JAtom>, head: Vec<JAtom>) -> JClause {
    JClause { body, head }
}

fn sub(left: &str, right: &str) -> JClause {
    clause(
        vec![concept(left, var("x"))],
        vec![concept(right, var("x"))],
    )
}

fn clean_ht_environment() {
    for name in [
        "KM_HT_CONTRA",
        "KM_HT_HARVEST",
        "KM_HT_LEARN",
        "KM_HT_LEARN_NOSTALE",
        "KM_HT_QO",
        "KM_HT_RESTART",
        "KM_HT_TRIGABS",
        "KM_NO_HT_EMELIM",
        "KM_TRIGGER_ABSORB",
    ] {
        std::env::remove_var(name);
    }
    std::env::set_var("KM_THREADS", "1");
}

fn canonical_unsat(
    mut result: kobayashi_marust::incremental::IncrementalResult,
) -> kobayashi_marust::incremental::IncrementalResult {
    for supers in result.subsumptions.values_mut() {
        if supers.iter().any(|candidate| candidate == "owl:Nothing") {
            supers.retain(|candidate| candidate == "owl:Nothing");
        }
    }
    result
}

fn assert_matches_fresh_cb(session: &IncrementalClassifier, clauses: &[JClause]) {
    let cb = classify_cb_fresh(clauses).expect("fresh CB oracle");
    assert_eq!(canonical_unsat(session.result()), canonical_unsat(cb));
    assert_eq!(
        session.result(),
        classify_ht_fresh(clauses).expect("fresh HT oracle")
    );
}

#[test]
fn forced_ht_addition_resumes_models_and_matches_fresh_classification() {
    let _env = env_lock();
    clean_ht_environment();

    let mut snapshot = vec![
        clause(
            vec![concept("A", var("x"))],
            vec![concept("B", var("x")), concept("C", var("x"))],
        ),
        sub("B", "D"),
        sub("C", "D"),
    ];
    let mut session =
        IncrementalClassifier::new_with_backend(snapshot.clone(), Some(IncrementalBackend::Ht))
            .expect("initial exact HT snapshot");
    assert_eq!(session.backend(), IncrementalBackend::Ht);
    assert_eq!(session.is_subsumed_by("A", "D"), Some(true));
    assert_matches_fresh_cb(&session, &snapshot);

    let update = session
        .add_clauses(vec![sub("D", "E")])
        .expect("monotone HT addition");
    snapshot.push(sub("D", "E"));
    assert_eq!(update.strategy, ChangeStrategy::HtDelta);
    assert!(update.reused_fixpoint);
    assert_eq!(session.is_subsumed_by("A", "E"), Some(true));
    assert_matches_fresh_cb(&session, &snapshot);
}

#[test]
fn ht_deletion_and_replacement_use_monotonic_evidence_and_dependency_rechecks() {
    let _env = env_lock();
    clean_ht_environment();

    let mut snapshot = vec![sub("A", "B"), sub("B", "C"), sub("X", "Y")];
    let mut session =
        IncrementalClassifier::new_with_backend(snapshot.clone(), Some(IncrementalBackend::Ht))
            .expect("initial HT snapshot");
    assert_matches_fresh_cb(&session, &snapshot);

    let addition = session
        .add_clauses(vec![sub("C", "D")])
        .expect("component-local addition");
    snapshot.push(sub("C", "D"));
    assert_eq!(addition.strategy, ChangeStrategy::HtDelta);
    assert!(addition.reused_subsumptions > 0);
    assert_matches_fresh_cb(&session, &snapshot);

    let removal = session
        .remove_clauses(&[2])
        .expect("dependency-directed removal");
    snapshot.remove(1);
    assert_eq!(removal.strategy, ChangeStrategy::HtDelta);
    assert_eq!(session.is_subsumed_by("A", "C"), Some(false));
    assert_eq!(session.is_subsumed_by("X", "Y"), Some(true));
    assert_matches_fresh_cb(&session, &snapshot);

    let replacement = session
        .apply_change(&[1], vec![sub("A", "Z")])
        .expect("atomic replacement");
    snapshot.remove(0);
    snapshot.push(sub("A", "Z"));
    assert_eq!(replacement.strategy, ChangeStrategy::HtDelta);
    assert_eq!(session.is_subsumed_by("A", "B"), Some(false));
    assert_eq!(session.is_subsumed_by("A", "Z"), Some(true));
    assert_matches_fresh_cb(&session, &snapshot);
}

#[test]
fn unsupported_ht_update_is_atomic_and_leaves_the_live_revision_usable() {
    let _env = env_lock();
    clean_ht_environment();

    let initial = vec![sub("A", "B")];
    let mut session =
        IncrementalClassifier::new_with_backend(initial.clone(), Some(IncrementalBackend::Ht))
            .expect("initial HT snapshot");
    let before = session.result();
    let before_ids = session.clause_ids();
    let before_revision = session.revision();

    let ground = clause(Vec::new(), vec![concept("B", ind("a"))]);
    assert!(matches!(
        session.add_clauses(vec![ground]),
        Err(IncrementalReasoningError::RequestedBackendUnsupported {
            backend: IncrementalBackend::Ht,
            ..
        })
    ));
    assert_eq!(session.result(), before);
    assert_eq!(session.clause_ids(), before_ids);
    assert_eq!(session.revision(), before_revision);

    let accepted = session
        .add_clauses(vec![sub("B", "C")])
        .expect("later valid update");
    assert_eq!(accepted.added_clause_ids, vec![2]);
    assert_eq!(session.is_subsumed_by("A", "C"), Some(true));
    assert_matches_fresh_cb(&session, &[initial[0].clone(), sub("B", "C")]);
}

#[test]
fn ht_addition_replay_clash_falls_back_to_an_exact_probe() {
    let _env = env_lock();
    clean_ht_environment();

    let mut snapshot = vec![sub("A", "B")];
    let mut session =
        IncrementalClassifier::new_with_backend(snapshot.clone(), Some(IncrementalBackend::Ht))
            .expect("initial HT snapshot");
    assert_eq!(session.is_subsumed_by("A", "owl:Nothing"), Some(false));

    // The retained A-model contains both A and B. This addition clashes with
    // that witness, which is only a failed SAT fast path, never an UNSAT proof.
    // The adapter must run a fresh exhaustive probe before publishing A as
    // unsatisfiable.
    let contradiction = clause(
        vec![concept("A", var("x")), concept("B", var("x"))],
        Vec::new(),
    );
    session
        .add_clauses(vec![contradiction.clone()])
        .expect("fresh fallback after replay clash");
    snapshot.push(contradiction);
    assert_eq!(session.is_subsumed_by("A", "owl:Nothing"), Some(true));
    assert_matches_fresh_cb(&session, &snapshot);
}

#[test]
fn ht_reuses_existential_graphs_and_rechecks_global_deletion() {
    let _env = env_lock();
    clean_ht_environment();

    let mut snapshot = vec![
        clause(
            vec![concept("A", var("x"))],
            vec![role("R", var("x"), fun("f"))],
        ),
        clause(vec![concept("A", var("x"))], vec![concept("B", fun("f"))]),
    ];
    let mut session =
        IncrementalClassifier::new_with_backend(snapshot.clone(), Some(IncrementalBackend::Ht))
            .expect("existential HT snapshot");
    assert_matches_fresh_cb(&session, &snapshot);

    let addition = session
        .add_clauses(vec![sub("B", "C")])
        .expect("addition over a retained existential graph");
    snapshot.push(sub("B", "C"));
    assert_eq!(addition.strategy, ChangeStrategy::HtDelta);
    assert!(addition.reused_fixpoint);
    assert!(addition.reused_edges > 0);
    assert_matches_fresh_cb(&session, &snapshot);

    let global_contradiction = clause(Vec::new(), Vec::new());
    let inconsistent = session
        .add_clauses(vec![global_contradiction.clone()])
        .expect("global contradiction");
    snapshot.push(global_contradiction);
    assert!(session.is_inconsistent());
    assert_matches_fresh_cb(&session, &snapshot);

    session
        .remove_clauses(&inconsistent.added_clause_ids)
        .expect("remove global contradiction");
    snapshot.pop();
    assert!(!session.is_inconsistent());
    assert_matches_fresh_cb(&session, &snapshot);
}

#[test]
fn jsonl_protocol_selects_ht_and_reports_ht_delta() {
    let _env = env_lock();
    clean_ht_environment();

    let initial = vec![sub("A", "B")];
    let addition = vec![sub("B", "C")];
    let input = format!(
        "{}\n{}\n{}\n",
        serde_json::json!({"op":"init","backend":"ht","clauses":initial}),
        serde_json::json!({"op":"add","clauses":addition}),
        serde_json::json!({"op":"is_subsumed_by","sub":"A","sup":"C"})
    );
    let mut child = Command::new(env!("CARGO_BIN_EXE_km"))
        .arg("incremental")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn incremental session");
    child
        .stdin
        .as_mut()
        .expect("stdin")
        .write_all(input.as_bytes())
        .expect("write session");
    drop(child.stdin.take());
    let output = child.wait_with_output().expect("wait for session");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let rows: Vec<serde_json::Value> = String::from_utf8(output.stdout)
        .unwrap()
        .lines()
        .map(|line| serde_json::from_str(line).unwrap())
        .collect();
    assert_eq!(rows[0]["backend"], "ht");
    assert_eq!(rows[1]["update"]["strategy"], "ht_delta");
    assert_eq!(rows[2]["entailed"], true);
}
