//! An inconsistent ontology gives every requested CB query the row
//! `owl:Nothing`, whatever the schedule (docs/PER-CONTEXT-ORDERING.md
//! section 13). From b88c6253 the one-shot paths of `Reasoner::saturate`
//! stop at a global refutation, so the rows of queries whose root context
//! the run never reached were missing: the fresh CB oracle answered
//! `{A: [owl:Nothing]}` for the ontology of
//! `incremental_ht_reasoning::ht_reuses_existential_graphs_and_rechecks_global_deletion`
//! while every class is unsatisfiable.
use std::sync::Mutex;

use kobayashi_marust::incremental::classify_cb_fresh;
use kobayashi_marust::json_io::{JAtom, JClause, JTerm};

static ENV_LOCK: Mutex<()> = Mutex::new(());

fn var() -> JTerm {
    JTerm::Var { name: "x".into() }
}

fn concept(name: &str, term: JTerm) -> JAtom {
    JAtom::Concept { concept: name.into(), term }
}

fn sub(left: &str, right: &str) -> JClause {
    JClause { body: vec![concept(left, var())], head: vec![concept(right, var())] }
}

fn ontology(extra: usize) -> (Vec<JClause>, Vec<String>) {
    let f = JTerm::Fun { function: "f".into(), arg: Box::new(var()) };
    let mut clauses = vec![
        JClause {
            body: vec![concept("A", var())],
            head: vec![JAtom::Role { role: "R".into(), source: var(), target: f.clone() }],
        },
        JClause { body: vec![concept("A", var())], head: vec![concept("B", f)] },
        sub("B", "C"),
    ];
    let mut names = vec!["A".to_string(), "B".to_string(), "C".to_string()];
    for i in 0..extra {
        let name = format!("K{i}");
        clauses.push(sub(&name, "C"));
        names.push(name);
    }
    // ⊤ ⊑ ⊥: the empty clause.
    clauses.push(JClause { body: Vec::new(), head: Vec::new() });
    (clauses, names)
}

#[test]
fn every_query_row_is_bottom_on_every_one_shot_path() {
    let _env = ENV_LOCK.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    for (threads, static_sched) in [("1", false), ("4", false), ("4", true)] {
        std::env::set_var("KM_THREADS", threads);
        if static_sched {
            std::env::set_var("KM_STATIC_SCHED", "1");
        } else {
            std::env::remove_var("KM_STATIC_SCHED");
        }
        for extra in [0, 40] {
            let (clauses, names) = ontology(extra);
            let result = classify_cb_fresh(&clauses).expect("fresh CB");
            assert!(result.inconsistent, "threads={threads} static={static_sched} extra={extra}");
            for name in &names {
                let row = result.subsumptions.get(name).unwrap_or_else(|| {
                    panic!("no row for {name}: threads={threads} static={static_sched} extra={extra}")
                });
                assert!(
                    row.iter().any(|s| s == "owl:Nothing"),
                    "{name} not below owl:Nothing: threads={threads} static={static_sched} extra={extra}"
                );
            }
        }
    }
    std::env::remove_var("KM_STATIC_SCHED");
    std::env::set_var("KM_THREADS", "1");
}

/// A consistent ontology keeps its rows: the completion reads the flag only.
#[test]
fn consistent_rows_are_unchanged() {
    let _env = ENV_LOCK.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    std::env::set_var("KM_THREADS", "1");
    let (mut clauses, _) = ontology(3);
    clauses.pop();
    let result = classify_cb_fresh(&clauses).expect("fresh CB");
    assert!(!result.inconsistent);
    assert!(result.subsumptions.values().all(|row| row.iter().all(|s| s != "owl:Nothing")));
    assert_eq!(result.subsumptions.get("B").cloned(), Some(vec!["C".to_string()]));
}
