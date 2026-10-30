//! Nominal CB loader: clauses whose body atoms are ground.
//!
//! The engine's Hyper binds a non-central body term like a variable, so a
//! ground body atom `D(a)` matched `D(t)` for every term `t`: adding the
//! entailed clause `__data__(a) → ⊥` to a satisfiable clause set made the
//! engine answer inconsistent. The loader now rewrites a clause whose body
//! atoms are all concept atoms on one individual into the central-guard
//! normal form `C₁(x) ∧ … ∧ Cₖ(x) → x ≉ a ∨ Δ[a/x]`, and drops (counts) any
//! other ground body atom.
use std::io::Write;
use std::process::{Command, Stdio};

fn engine(clauses: &str) -> serde_json::Value {
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars_os() {
        if key.to_string_lossy().starts_with("KM_") {
            command.env_remove(key);
        }
    }
    let mut child = command
        .arg("engine")
        .env("KM_NOMINALS", "1")
        .env("KM_THREADS", "1")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child.stdin.take().unwrap().write_all(clauses.as_bytes()).unwrap();
    let output = child.wait_with_output().unwrap();
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    serde_json::from_slice(&output.stdout).unwrap()
}

fn x() -> &'static str {
    r#"{"kind":"var","name":"x"}"#
}
fn y() -> &'static str {
    r#"{"kind":"var","name":"y"}"#
}
fn ind(name: &str) -> String {
    format!(r#"{{"kind":"ind","name":"{name}"}}"#)
}
fn c(concept: &str, term: &str) -> String {
    format!(r#"{{"kind":"concept","concept":"{concept}","term":{term}}}"#)
}
fn role(name: &str, s: &str, t: &str) -> String {
    format!(r#"{{"kind":"role","role":"{name}","source":{s},"target":{t}}}"#)
}
fn fx() -> &'static str {
    r#"{"kind":"fun","function":"f_Q_0_0","arg":{"kind":"var","name":"x"}}"#
}
fn clause(body: &[String], head: &[String]) -> String {
    format!(r#"{{"body":[{}],"head":[{}]}}"#, body.join(","), head.join(","))
}
fn input(clauses: &[String], named: &[&str]) -> String {
    let named: Vec<String> = named.iter().map(|n| format!("\"{n}\"")).collect();
    format!(r#"{{"clauses":[{}],"named":[{}]}}"#, clauses.join(","), named.join(","))
}

/// The bug-1 agent's `cm4`: every individual is an object (`Has(a)` and
/// `Has ∧ __data__ → ⊥`), so the extra clause `__data__(a) → ⊥` is entailed
/// and must not change the answer: consistent, `Has` satisfiable.
#[test]
fn entailed_ground_negative_fact_keeps_the_answer() {
    let mut base = vec![
        clause(&[], &[c("Q_1", x())]),
        clause(&[c("Q_0", x())], &[role("d", x(), fx())]),
        clause(&[c("Q_0", x())], &[c("Q_1", fx())]),
        clause(&[c("Q_1", y()), role("d", x(), y())], &[c("Q_0", x())]),
        clause(&[c("Has", x())], &[c("Q_0", x())]),
        clause(&[c("Q_0", x())], &[c("Has", x())]),
        clause(&[c("Q_1", x())], &[c("Q_2", x()), c("__data__", x())]),
        clause(&[], &[c("Has", &ind("a"))]),
        clause(&[c("Has", x()), c("__data__", x())], &[]),
        clause(&[c("Q_0", x()), c("__data__", x())], &[]),
        clause(&[c("Q_2", x()), c("__data__", x())], &[]),
        clause(&[c("__data__", x()), role("d", x(), y())], &[]),
        clause(&[role("d", x(), y())], &[c("__data__", y())]),
    ];
    let without = engine(&input(&base, &["Has"]));
    base.push(clause(&[c("__data__", &ind("a"))], &[]));
    let with = engine(&input(&base, &["Has"]));
    for answer in [&without, &with] {
        assert_eq!(answer["inconsistent"], false, "{answer}");
        assert_eq!(answer["dropped"], 0, "{answer}");
        let has = answer["subsumptions"]["Has"].as_array().cloned().unwrap_or_default();
        assert!(!has.iter().any(|s| s == "owl:Nothing"), "{answer}");
    }
}

/// The rewritten clause fires exactly at its individual: `C(a) → D(b)` with
/// `D ⊑ ⊥` is inconsistent when `C(a)` holds, and consistent when only some
/// other individual is `C`.
#[test]
fn guarded_ground_clause_fires_only_at_its_individual() {
    let rule = clause(&[c("C", &ind("a"))], &[c("D", &ind("b"))]);
    let bottom = clause(&[c("D", x())], &[]);
    let fires = engine(&input(&[clause(&[], &[c("C", &ind("a"))]), rule.clone(), bottom.clone()], &["C", "D"]));
    assert_eq!(fires["inconsistent"], true, "{fires}");
    let other = engine(&input(&[clause(&[], &[c("C", &ind("c"))]), rule, bottom], &["C", "D"]));
    assert_eq!(other["inconsistent"], false, "{other}");
    assert_eq!(other["dropped"], 0, "{other}");
}

/// A ground body atom outside the single-individual shape is dropped and
/// counted, never silently.
#[test]
fn unsupported_ground_body_is_counted_as_dropped() {
    let answer = engine(&input(
        &[clause(&[], &[c("C", &ind("a"))]), clause(&[c("C", &ind("a")), c("E", &ind("b"))], &[])],
        &["C"],
    ));
    assert_eq!(answer["dropped"], 1, "{answer}");
}
