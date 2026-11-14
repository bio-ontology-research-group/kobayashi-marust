//! `km classify --properties`: the object property hierarchy, domains and
//! ranges.
//!
//! Expected rows in `fixtures/properties/*.rows` were produced by HermiT 1.4.3
//! through the OWL API (`getSuperObjectProperties`, `getEquivalentObjectProperties`,
//! `getObjectPropertyDomains` and `getObjectPropertyRanges`, cross-checked by
//! `isEntailed`) in the row convention of docs/PROPERTIES.md, and are fixed
//! here as independent oracles. Where HermiT misses an entailment, the
//! fixture holds the entailed rows and says so in a `#` comment line.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const CASES: &[&str] = &["chain", "inverse", "symmetric", "empty", "nominal", "domrange_nominal", "inconsistent", "inverse_free"];

const PROPERTY_ROWS: &[&str] = &["SUBPROP\t", "TOPPROP\t", "BOTPROP\t", "DOMAIN\t", "RANGE\t"];

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/properties").join(name)
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

fn is_property_row(line: &str) -> bool {
    PROPERTY_ROWS.iter().any(|kind| line.starts_with(kind))
}

fn property_rows(text: &str) -> BTreeSet<String> {
    text.lines().filter(|line| is_property_row(line)).map(str::to_string).collect()
}

fn expected(name: &str) -> BTreeSet<String> {
    std::fs::read_to_string(fixture(name))
        .unwrap()
        .lines()
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .map(str::to_string)
        .collect()
}

#[test]
fn properties_report_the_hierarchy_domains_and_ranges() {
    for case in CASES {
        let source = fixture(&format!("{case}.ofn"));
        let plain = stdout(&km(&source, &["--lines"]));
        let extended = stdout(&km(&source, &["--lines", "--properties"]));
        assert_eq!(property_rows(&extended), expected(&format!("{case}.rows")), "{case}");
        // The taxonomy part is the plain classification, byte for byte, and
        // the property rows follow it.
        assert!(extended.starts_with(&plain[..plain.len() - 1]), "{case}: taxonomy prefix differs");
        let taxonomy: Vec<&str> = extended.lines().filter(|line| !is_property_row(line)).collect();
        assert_eq!(taxonomy, plain.lines().collect::<Vec<_>>(), "{case}");
    }
}

#[test]
fn inconsistent_ontology_reports_no_property_rows() {
    let extended = stdout(&km(&fixture("inconsistent.ofn"), &["--lines", "--properties"]));
    assert!(extended.starts_with("CONSISTENT 0\n"), "{extended}");
    assert!(property_rows(&extended).is_empty());
}

#[test]
fn json_properties_add_only_the_property_keys() {
    let source = fixture("inverse.ofn");
    let plain: serde_json::Value = serde_json::from_slice(&km(&source, &[]).stdout).unwrap();
    let output = km(&source, &["--properties"]);
    assert!(output.status.success());
    let mut extended: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    let object = extended.as_object_mut().unwrap();
    let sub = object.remove("subproperties").unwrap();
    let top = object.remove("topproperties").unwrap();
    let bottom = object.remove("bottomproperties").unwrap();
    let domains = object.remove("domains").unwrap();
    let ranges = object.remove("ranges").unwrap();
    assert_eq!(extended, plain);
    assert!(sub.as_array().unwrap().contains(&serde_json::json!(["urn:t#hasComponent", "ObjectInverseOf(urn:t#partOf)"])));
    assert_eq!(top, serde_json::json!([]));
    assert_eq!(bottom, serde_json::json!([]));
    assert!(domains.as_array().unwrap().contains(&serde_json::json!(["urn:t#partOf", "urn:t#Part"])));
    assert!(ranges.as_array().unwrap().contains(&serde_json::json!(["urn:t#hasComponent", "urn:t#Part"])));
}

#[test]
fn properties_combine_with_realize_in_one_run() {
    let source = fixture("nominal.ofn");
    let realized = stdout(&km(&source, &["--lines", "--realize"]));
    let properties = stdout(&km(&source, &["--lines", "--properties"]));
    let both = stdout(&km(&source, &["--lines", "--realize", "--properties"]));
    // Realization rows first, then property rows.
    assert!(both.starts_with(&realized[..realized.len() - 1]), "{both}");
    assert_eq!(property_rows(&both), property_rows(&properties));
    let json: serde_json::Value = serde_json::from_slice(&km(&source, &["--realize", "--properties"]).stdout).unwrap();
    for key in ["types", "same", "subproperties", "domains"] {
        assert!(json.get(key).is_some(), "{key}");
    }
}

#[test]
fn properties_options_are_validated() {
    let source = fixture("chain.ofn");
    let output = km(&source, &["--properties", "--json-edges"]);
    assert_eq!(output.status.code(), Some(2));
    assert!(output.stdout.is_empty());
    let forced = km(&source, &["--lines", "--properties", "--route", "elc"]);
    assert_eq!(forced.status.code(), Some(3), "{}", String::from_utf8_lossy(&forced.stderr));
    let help = km(&source, &["--help"]);
    assert!(String::from_utf8_lossy(&help.stdout).contains("SUBPROP<TAB>r<TAB>f"));
}

/// `ObjectPropertyDomain(e owl:Nothing)` and `ObjectPropertyRange(f owl:Nothing)`
/// make `e` and `f` empty (bug E7: the frontend used to drop both axioms).
#[test]
fn domain_or_range_nothing_empties_the_property() {
    let source = fixture("domain_nothing.ofn");
    let extended = stdout(&km(&source, &["--lines", "--properties"]));
    assert_eq!(property_rows(&extended), expected("domain_nothing.rows"));
}

/// An inverse-free source takes its ranges from a second run with fresh
/// asserted pairs (docs/PROPERTIES.md). Those individuals never reach the
/// output: `--realize --properties` reports the source individuals only.
#[test]
fn range_run_individuals_stay_internal() {
    let source = fixture("inverse_free.ofn");
    let realized = stdout(&km(&source, &["--lines", "--realize"]));
    let both = stdout(&km(&source, &["--lines", "--realize", "--properties"]));
    assert!(both.starts_with(&realized[..realized.len() - 1]), "{both}");
    assert_eq!(property_rows(&both), expected("inverse_free.rows"));
    assert!(!both.contains("km.invalid"), "{both}");
    let types: Vec<&str> = both.lines().filter(|line| line.starts_with("TYPE\t")).collect();
    assert_eq!(types, ["TYPE\t:a\t:A", "TYPE\t:b\t:B", "TYPE\t:b\t:C"]);
}
