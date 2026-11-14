//! `km classify --top`: the named classes equivalent to `owl:Thing`.
//!
//! Expected `TOP` rows in `fixtures/top/*.rows` were produced by HermiT 1.4.3
//! (`getTopClassNode()` through the OWL API) and are fixed here as oracles.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const CASES: &[&str] = &[
    "top-union", "top-none", "top-axiom", "top-tautology", "top-universal", "top-abox",
    "top-inconsistent", "top-unsat",
];

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/top").join(name)
}

fn km(path: &Path, options: &[&str]) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars() {
        if key.starts_with("KM_") {
            command.env_remove(key);
        }
    }
    command.env("KM_THREADS", "1");
    command.arg("classify").args(options).arg(path);
    command.output().unwrap()
}

fn stdout(output: &Output) -> String {
    assert!(output.status.success(), "km failed: {}", String::from_utf8_lossy(&output.stderr));
    String::from_utf8(output.stdout.clone()).unwrap()
}

fn top_rows(text: &str) -> BTreeSet<String> {
    text.lines().filter(|line| line.starts_with("TOP\t")).map(str::to_string).collect()
}

fn expected(case: &str) -> BTreeSet<String> {
    std::fs::read_to_string(fixture(&format!("{case}.rows")))
        .unwrap()
        .lines()
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .map(str::to_string)
        .collect()
}

#[test]
fn top_rows_match_hermit_and_keep_the_taxonomy() {
    for case in CASES {
        let source = fixture(&format!("{case}.ofn"));
        let plain = stdout(&km(&source, &["--lines"]));
        assert!(top_rows(&plain).is_empty(), "{case}: default output has no TOP rows");
        let top = stdout(&km(&source, &["--lines", "--top"]));
        assert_eq!(top_rows(&top), expected(case), "{case}");
        let taxonomy: Vec<&str> = top.lines().filter(|line| !line.starts_with("TOP\t")).collect();
        assert_eq!(taxonomy, plain.lines().collect::<Vec<_>>(), "{case}");
    }
}

#[test]
fn top_combines_with_realize_and_properties() {
    for case in ["top-abox", "top-union", "top-universal"] {
        let source = fixture(&format!("{case}.ofn"));
        let both = stdout(&km(&source, &["--lines", "--realize", "--properties"]));
        let all = stdout(&km(&source, &["--lines", "--realize", "--properties", "--top"]));
        assert_eq!(top_rows(&all), expected(case), "{case}");
        let rest: Vec<&str> = all.lines().filter(|line| !line.starts_with("TOP\t")).collect();
        assert_eq!(rest, both.lines().collect::<Vec<_>>(), "{case}");
    }
}

#[test]
fn json_top_key_only_with_the_flag() {
    let source = fixture("top-union.ofn");
    let plain: serde_json::Value = serde_json::from_slice(&km(&source, &[]).stdout).unwrap();
    assert!(plain.get("top").is_none());
    let output = km(&source, &["--top"]);
    assert!(output.status.success());
    let mut extended: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    let top = extended.as_object_mut().unwrap().remove("top").unwrap();
    assert_eq!(extended, plain);
    assert_eq!(top, serde_json::json!([":C", ":E"]));
}

#[test]
fn inconsistent_ontology_has_no_top_rows() {
    let out = stdout(&km(&fixture("top-inconsistent.ofn"), &["--lines", "--top"]));
    assert!(out.starts_with("CONSISTENT 0\n"), "{out}");
    assert!(top_rows(&out).is_empty());
}
