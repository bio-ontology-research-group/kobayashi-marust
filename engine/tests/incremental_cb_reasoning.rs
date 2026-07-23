use std::collections::BTreeMap;
use std::io::Write;
use std::process::{Command, Stdio};
use std::sync::Mutex;

use kobayashi_marust::incremental::{
    classify_fresh, ChangeStrategy, IncrementalBackend, IncrementalClassifier,
    IncrementalReasoningError, IncrementalResult,
};
use kobayashi_marust::json_io::{JAtom, JClause, JTerm};

static ENV_LOCK: Mutex<()> = Mutex::new(());

fn var(name: &str) -> JTerm {
    JTerm::Var {
        name: name.to_string(),
    }
}

fn fun(function: &str) -> JTerm {
    JTerm::Fun {
        function: function.to_string(),
        arg: Box::new(var("x")),
    }
}

fn ind(name: &str) -> JTerm {
    JTerm::Ind {
        name: name.to_string(),
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

fn equality(left: JTerm, right: JTerm) -> JAtom {
    JAtom::Eq { left, right }
}

fn clause(body: Vec<JAtom>, head: Vec<JAtom>) -> JClause {
    JClause { body, head }
}

fn fresh_worker(clauses: &[JClause], worker: &str, nominals: bool) -> IncrementalResult {
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    command
        .arg(worker)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .env("KM_THREADS", "1")
        .env_remove("KM_ELC_CERT")
        .env_remove("KM_ENGINE_MAX_CONTEXTS")
        .env_remove("KM_ENGINE_MAX_CLAUSES")
        .env_remove("KM_MSG_CAP")
        .env_remove("KM_NOM_BUDGET")
        .env_remove("KM_NOMINALS");
    if nominals {
        command.env("KM_NOMINALS", "1");
    }
    let mut child = command.spawn().expect("spawn fresh KM worker");
    serde_json::to_writer(
        child.stdin.as_mut().expect("worker stdin"),
        &serde_json::json!({"clauses": clauses}),
    )
    .expect("write fresh worker input");
    child
        .stdin
        .take()
        .expect("close worker stdin")
        .flush()
        .unwrap();
    let output = child.wait_with_output().expect("wait for fresh KM worker");
    assert!(
        output.status.success(),
        "fresh {worker} failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let value: serde_json::Value =
        serde_json::from_slice(&output.stdout).expect("fresh worker JSON output");
    let subsumptions: BTreeMap<String, Vec<String>> =
        serde_json::from_value(value["subsumptions"].clone()).expect("subsumption map");
    let dropped = value["dropped"].as_u64().unwrap_or(0) as usize;
    assert_eq!(dropped, 0, "fresh worker unexpectedly dropped clauses");
    IncrementalResult {
        subsumptions,
        inconsistent: value["inconsistent"].as_bool().expect("consistency flag"),
        dropped,
        unresolved: value["unresolved"]
            .as_array()
            .map(|items| {
                items
                    .iter()
                    .map(|item| item.as_str().unwrap().to_string())
                    .collect()
            })
            .unwrap_or_default(),
    }
}

fn assert_fresh_cb(session: &IncrementalClassifier, snapshot: &[JClause], nominals: bool) {
    let fresh = fresh_worker(snapshot, "engine", nominals);
    assert_eq!(session.result(), fresh);
}

fn assert_fresh_route(session: &IncrementalClassifier, snapshot: &[JClause]) {
    let (backend, fresh) = classify_fresh(snapshot).expect("fresh exact route");
    assert_eq!(session.backend(), backend);
    assert_eq!(session.result(), fresh);
}

#[test]
fn cb_additions_removals_and_rejections_match_every_fresh_fixpoint() {
    let _env = ENV_LOCK.lock().unwrap();
    std::env::set_var("KM_THREADS", "1");
    std::env::remove_var("KM_ELC_CERT");
    std::env::remove_var("KM_MSG_CAP");
    std::env::remove_var("KM_NOM_BUDGET");
    std::env::remove_var("KM_NOMINALS");

    let disjunction = clause(
        vec![concept("A", var("x"))],
        vec![concept("B", var("x")), concept("C", var("x"))],
    );
    let b_to_d = clause(vec![concept("B", var("x"))], vec![concept("D", var("x"))]);
    let c_to_d = clause(vec![concept("C", var("x"))], vec![concept("D", var("x"))]);
    let mut snapshot = vec![disjunction.clone()];
    let mut session = IncrementalClassifier::new(snapshot.clone()).expect("CB snapshot");
    assert_eq!(session.backend(), IncrementalBackend::Cb);
    assert_fresh_cb(&session, &snapshot, false);

    let update = session
        .add_clauses(vec![b_to_d.clone(), c_to_d.clone()])
        .expect("CB addition");
    snapshot.extend([b_to_d.clone(), c_to_d.clone()]);
    assert_eq!(update.strategy, ChangeStrategy::ExactRebuild);
    assert_eq!(update.added_clause_ids, vec![2, 3]);
    assert_eq!(session.is_subsumed_by("A", "D"), Some(true));
    assert_fresh_cb(&session, &snapshot, false);

    let removal = session.remove_clauses(&[2]).expect("CB removal");
    snapshot.remove(1);
    assert_eq!(removal.strategy, ChangeStrategy::ExactRebuild);
    assert_eq!(session.is_subsumed_by("A", "D"), Some(false));
    assert_fresh_cb(&session, &snapshot, false);

    let removal = session.remove_clauses(&[1]).expect("CB to EL removal");
    snapshot.remove(0);
    assert_eq!(removal.backend_before, IncrementalBackend::Cb);
    assert_eq!(removal.backend_after, IncrementalBackend::El);
    assert_eq!(session.clause_ids(), vec![3]);
    assert_fresh_route(&session, &snapshot);

    let update = session
        .add_clauses(vec![disjunction.clone()])
        .expect("EL to CB addition");
    snapshot.push(disjunction);
    assert_eq!(update.added_clause_ids, vec![4]);
    assert_eq!(update.backend_after, IncrementalBackend::Cb);
    assert_fresh_cb(&session, &snapshot, false);

    let replacement = clause(
        vec![concept("A", var("x"))],
        vec![concept("B", var("x")), concept("E", var("x"))],
    );
    let update = session
        .apply_change(&[4], vec![replacement.clone()])
        .expect("atomic CB replacement");
    snapshot.pop();
    snapshot.push(replacement);
    assert_eq!(update.revision, 5);
    assert_eq!(update.removed_clause_ids, vec![4]);
    assert_eq!(update.added_clause_ids, vec![5]);
    assert_eq!(session.clause_ids(), vec![3, 5]);
    assert_fresh_cb(&session, &snapshot, false);

    let before = session.result();
    let before_revision = session.revision();
    let unsupported = clause(
        Vec::new(),
        vec![concept(
            "Unsupported",
            JTerm::Aux {
                root: "r".to_string(),
                label: Vec::new(),
            },
        )],
    );
    assert_eq!(
        session.apply_change(&[5], vec![unsupported]),
        Err(IncrementalReasoningError::UnsupportedClauses { dropped: 1 })
    );
    assert_eq!(session.revision(), before_revision);
    assert_eq!(session.result(), before);
    assert_eq!(session.clause_ids(), vec![3, 5]);

    assert_eq!(
        session.remove_clauses(&[5, 5]),
        Err(IncrementalReasoningError::DuplicateClauseIds { ids: vec![5] })
    );
    assert_eq!(
        session.remove_clauses(&[999]),
        Err(IncrementalReasoningError::UnknownClauseIds { ids: vec![999] })
    );
    assert_eq!(session.revision(), before_revision);
    assert_eq!(session.result(), before);
}

#[test]
fn roles_chains_and_cardinality_equalities_match_fresh_batches() {
    let _env = ENV_LOCK.lock().unwrap();
    std::env::set_var("KM_THREADS", "1");
    std::env::remove_var("KM_ELC_CERT");
    std::env::remove_var("KM_MSG_CAP");
    std::env::remove_var("KM_NOM_BUDGET");
    std::env::remove_var("KM_NOMINALS");

    let role_chain_snapshot = vec![
        clause(
            vec![concept("A", var("x"))],
            vec![role("R", var("x"), fun("f"))],
        ),
        clause(vec![concept("A", var("x"))], vec![concept("B", fun("f"))]),
        clause(
            vec![concept("B", var("x"))],
            vec![role("S", var("x"), fun("g"))],
        ),
        clause(vec![concept("B", var("x"))], vec![concept("C", fun("g"))]),
        clause(
            vec![role("R", var("x"), var("y")), role("S", var("y"), var("z"))],
            vec![role("T", var("x"), var("z"))],
        ),
        clause(
            vec![role("T", var("x"), var("y")), concept("C", var("y"))],
            vec![concept("D", var("x"))],
        ),
    ];
    let mut chain_session =
        IncrementalClassifier::new(role_chain_snapshot[..4].to_vec()).expect("initial EL roles");
    assert_fresh_route(&chain_session, &role_chain_snapshot[..4]);
    let update = chain_session
        .add_clauses(role_chain_snapshot[4..].to_vec())
        .expect("EL role-chain addition");
    assert_eq!(update.strategy, ChangeStrategy::ElDelta);
    assert_eq!(chain_session.is_subsumed_by("A", "D"), Some(true));
    assert_fresh_route(&chain_session, &role_chain_snapshot);
    assert_eq!(
        chain_session.result(),
        fresh_worker(&role_chain_snapshot, "elc", false)
    );
    chain_session
        .remove_clauses(&update.added_clause_ids)
        .expect("role-chain removal");
    assert_fresh_route(&chain_session, &role_chain_snapshot[..4]);

    let distinct = clause(
        vec![concept("Q", var("x")), equality(fun("f"), fun("g"))],
        Vec::new(),
    );
    let at_most = clause(
        vec![concept("Q", var("x"))],
        vec![equality(fun("f"), fun("g"))],
    );
    let mut cardinality_snapshot = vec![
        clause(
            vec![concept("Q", var("x"))],
            vec![role("R", var("x"), fun("f"))],
        ),
        clause(
            vec![concept("Q", var("x"))],
            vec![role("R", var("x"), fun("g"))],
        ),
        distinct,
    ];
    let mut cardinality_session = IncrementalClassifier::new(cardinality_snapshot.clone())
        .expect("CB number-restriction normal forms");
    assert_eq!(cardinality_session.backend(), IncrementalBackend::Cb);
    assert_fresh_cb(&cardinality_session, &cardinality_snapshot, false);
    let update = cardinality_session
        .add_clauses(vec![at_most.clone()])
        .expect("at-most equality addition");
    cardinality_snapshot.push(at_most);
    assert_eq!(
        cardinality_session.is_subsumed_by("Q", "owl:Nothing"),
        Some(true)
    );
    assert_fresh_cb(&cardinality_session, &cardinality_snapshot, false);
    cardinality_session
        .remove_clauses(&update.added_clause_ids)
        .expect("at-most equality removal");
    cardinality_snapshot.pop();
    assert_eq!(
        cardinality_session.is_subsumed_by("Q", "owl:Nothing"),
        Some(false)
    );
    assert_fresh_cb(&cardinality_session, &cardinality_snapshot, false);
}

#[test]
fn nominal_updates_match_fresh_nominal_cb() {
    let _env = ENV_LOCK.lock().unwrap();
    std::env::set_var("KM_THREADS", "1");
    std::env::remove_var("KM_ELC_CERT");
    std::env::remove_var("KM_MSG_CAP");
    std::env::remove_var("KM_NOM_BUDGET");
    std::env::set_var("KM_NOMINALS", "1");
    let nominal_fact = clause(Vec::new(), vec![concept("B", ind("a"))]);
    let nominal_link = clause(
        vec![concept("A", var("x"))],
        vec![equality(var("x"), ind("a"))],
    );
    let b_to_c = clause(vec![concept("B", var("x"))], vec![concept("C", var("x"))]);
    let mut snapshot = vec![nominal_fact, nominal_link];
    let mut session = IncrementalClassifier::new(snapshot.clone()).expect("nominal CB snapshot");
    assert_eq!(session.backend(), IncrementalBackend::Cb);
    assert_fresh_cb(&session, &snapshot, true);
    let update = session
        .add_clauses(vec![b_to_c.clone()])
        .expect("nominal CB addition");
    snapshot.push(b_to_c);
    assert_fresh_cb(&session, &snapshot, true);
    session
        .remove_clauses(&update.added_clause_ids)
        .expect("nominal CB removal");
    snapshot.pop();
    assert_fresh_cb(&session, &snapshot, true);
    std::env::remove_var("KM_NOMINALS");
}
