//! `km classify --iris full` (GitHub issue #8, docs/INPUT-FORMATS.md,
//! "Entity names in output"): one ontology written four ways (Functional
//! Syntax with prefixes, Functional Syntax with full IRIs, OWL/XML with
//! abbreviated IRIs, Turtle) gives byte-identical output, every entity named
//! by its full IRI. The default output keeps the source spelling.
use std::path::{Path, PathBuf};
use std::process::Command;

const INPUTS: [&str; 4] = ["prefixed.ofn", "full.ofn", "abbreviated.owx", "turtle.ttl"];

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/iris_full").join(name)
}

fn km(input: &str, options: &[&str], env: &[(&str, &str)]) -> String {
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars_os() {
        if key.to_string_lossy().starts_with("KM_") {
            command.env_remove(key);
        }
    }
    command.env("KM_THREADS", "1");
    for (key, value) in env {
        command.env(key, value);
    }
    let output = command.arg("classify").args(options).arg(fixture(input)).output().unwrap();
    assert!(output.status.success(), "{input} {options:?}: {}", String::from_utf8_lossy(&output.stderr));
    String::from_utf8(output.stdout).unwrap()
}

fn same_across_syntaxes(options: &[&str]) -> String {
    let reference = km(INPUTS[0], options, &[]);
    for input in &INPUTS[1..] {
        assert_eq!(km(input, options, &[]), reference, "{input} {options:?}");
    }
    reference
}

const EXTENDED: [&str; 7] = ["--iris", "full", "--lines", "--realize", "--values", "--different", "--properties"];

#[test]
fn full_iris_are_identical_across_syntaxes_in_json() {
    let json = same_across_syntaxes(&["--iris", "full"]);
    assert!(json.contains("[\"http://example.org/A\", \"http://example.org/B\"]"), "{json}");
    assert!(json.contains("\"http://example.org/D\""), "{json}");
    assert!(!json.contains("\"ex:") && !json.contains("\":a\""), "{json}");
}

#[test]
fn full_iris_are_identical_across_syntaxes_in_extended_lines() {
    let lines = same_across_syntaxes(&EXTENDED);
    for row in [
        "SUB\thttp://example.org/A\thttp://example.org/B",
        "UNSAT\thttp://example.org/D",
        "TYPE\thttp://example.org/i#a\thttp://example.org/A",
        "TYPE\thttp://example.org/i#a\thttp://example.org/C",
        "SAME\thttp://example.org/i#b\thttp://example.org/i#c",
        "VALUE\thttp://example.org/r\thttp://example.org/i#a\thttp://example.org/i#b",
        "DIFFERENT\thttp://example.org/i#a\thttp://example.org/i#b",
        "SUBPROP\thttp://example.org/r\thttp://example.org/s",
        "DOMAIN\thttp://example.org/r\thttp://example.org/C",
    ] {
        assert!(lines.lines().any(|line| line == row), "missing {row:?} in\n{lines}");
    }
    assert!(!lines.contains("ex:") && !lines.contains("\t:"), "{lines}");
}

#[test]
fn full_iris_are_identical_across_syntaxes_for_graph_edges_and_data_properties() {
    same_across_syntaxes(&["--iris", "full", "--json-edges"]);
    same_across_syntaxes(&["--iris", "full", "--lines", "--data-properties", "--top"]);
    same_across_syntaxes(&["--iris=full", "--lines"]);
}

#[test]
fn environment_selects_full_iris_and_the_flag_overrides_it() {
    let flag = km("prefixed.ofn", &["--iris", "full", "--lines"], &[]);
    assert_eq!(km("prefixed.ofn", &["--lines"], &[("KM_IRIS", "full")]), flag);
    assert_eq!(
        km("prefixed.ofn", &["--iris", "source", "--lines"], &[("KM_IRIS", "full")]),
        km("prefixed.ofn", &["--lines"], &[])
    );
}

#[test]
fn default_output_keeps_the_source_spelling() {
    let lines = km("prefixed.ofn", &["--lines"], &[]);
    assert!(lines.lines().any(|line| line == "SUB\tex:A\tex:B"), "{lines}");
    assert_eq!(km("prefixed.ofn", &["--iris", "source", "--lines"], &[]), lines);
    let full = km("full.ofn", &["--lines"], &[]);
    assert!(full.lines().any(|line| line == "SUB\thttp://example.org/A\thttp://example.org/B"), "{full}");
}

#[test]
fn unknown_iris_value_is_refused() {
    let output = Command::new(env!("CARGO_BIN_EXE_km"))
        .args(["classify", "--iris", "short"])
        .arg(fixture("prefixed.ofn"))
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&output.stderr).contains("--iris takes source or full"));
}
