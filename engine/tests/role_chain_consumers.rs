//! Consumers of roles whose language contains a role-chain word (E12).
//!
//! The CB clause stream never materializes chain edges. Before the complete
//! role-automaton encoding (`preprocess::chain_consumer_automaton_clauses`),
//! `∀`-consumers, ranges, consumers of inverses of chain targets and
//! negated existentials over such roles lost their chain consequences, on
//! every route that fell back to CB (all chains of three or more roles, which
//! the native bridge fences, and every nominal input). Expected rows in
//! `fixtures/chains/*.rows` were produced by HermiT 1.4.3 through the OWL API
//! and are fixed here as oracles.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const CASES: &[&str] = &[
    "chain2-inverse-nominal",
    "chain3-inverse-nominal",
    "chain3-inverse-property-nominal",
    "chain4-inverse-nominal",
    "chain3-through-nominal",
    "chain3-through-nominal-abox",
    "chain3-forall",
    "chain3-inverse-forall",
    "chain3-inverse-back",
    "chain3-transitive-forall",
    "chain3-transitive-middle",
    "chain3-inverse-nominal-both",
    "chain2-forall-inverse-of-target",
    "chain2-exists-inverse-of-target",
    "chain3-forall-inverse-of-target",
    "chain3-inverse-properties-forall",
    "chain5-forall",
    "chain3-range",
    "chain3-domain",
    "chain3-negated-exists",
    "chain3-super-role-forall",
    "chain-left-recursive-forall",
    "chain3-forall-disjunction",
    "chain3-forall-in-disjunction",
    "chain2-forall-disjunctive-tbox",
    "transitive-forall",
];

/// Inputs without individuals: the plain CB worker alone must also be exact.
const NOMINAL_FREE: &[&str] = &[
    "chain3-forall",
    "chain3-inverse-forall",
    "chain3-inverse-back",
    "chain3-transitive-forall",
    "chain3-transitive-middle",
    "chain2-forall-inverse-of-target",
    "chain2-exists-inverse-of-target",
    "chain3-forall-inverse-of-target",
    "chain3-inverse-properties-forall",
    "chain5-forall",
    "chain3-range",
    "chain3-domain",
    "chain3-negated-exists",
    "chain3-super-role-forall",
    "chain-left-recursive-forall",
    "chain3-forall-disjunction",
    "chain3-forall-in-disjunction",
    "chain2-forall-disjunctive-tbox",
    "transitive-forall",
];

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/chains").join(name)
}

fn km(path: &Path, options: &[&str]) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars() {
        if key.starts_with("KM_") {
            command.env_remove(key);
        }
    }
    command.env("KM_THREADS", "1");
    command.arg("classify").arg("--lines").args(options).arg(path);
    command.output().unwrap()
}

fn rows(text: &str) -> BTreeSet<String> {
    text.lines()
        .filter(|line| {
            line.starts_with("CONSISTENT ") || line.starts_with("SUB\t") || line.starts_with("UNSAT\t")
        })
        .map(str::to_string)
        .collect()
}

fn check(case: &str, options: &[&str]) {
    let output = km(&fixture(&format!("{case}.ofn")), options);
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        output.status.success(),
        "{case} {options:?}: km failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(stdout.lines().any(|line| line == "DROPPED 0"), "{case} {options:?}: {stdout}");
    let expected = rows(&std::fs::read_to_string(fixture(&format!("{case}.rows"))).unwrap());
    assert_eq!(rows(&stdout), expected, "{case} {options:?}");
}

#[test]
fn automatic_route_matches_hermit() {
    for case in CASES {
        check(case, &[]);
    }
}

#[test]
fn nominal_cb_route_matches_hermit() {
    for case in CASES {
        check(case, &["--route", "nominals"]);
    }
}

#[test]
fn plain_cb_route_matches_hermit_without_individuals() {
    for case in NOMINAL_FREE {
        check(case, &["--route", "cb_plain1"]);
    }
}
