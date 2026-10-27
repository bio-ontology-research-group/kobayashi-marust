//! `km classify --realize`: TYPE and SAME rows for named individuals.
//!
//! Expected rows in `fixtures/realization/*.all` and `*.direct` were produced
//! by HermiT 1.4 (`getTypes(a, false|true)` without `owl:Thing`, and
//! `getSameIndividuals`) and are fixed here as independent oracles.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const CASES: &[&str] = &["exists_forall", "chain", "functional", "sameas", "inconsistent", "cases"];

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/realization").join(name)
}

fn km(path: &Path, options: &[&str]) -> Output {
    km_env(path, options, &[])
}

fn km_env(path: &Path, options: &[&str], environment: &[(&str, &str)]) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars() {
        if key.starts_with("KM_") {
            command.env_remove(key);
        }
    }
    command.env("KM_THREADS", "1").envs(environment.iter().copied());
    command.arg("classify").args(options).arg(path);
    command.output().unwrap()
}

fn stdout(output: &Output) -> String {
    assert!(output.status.success(), "km failed: {}", String::from_utf8_lossy(&output.stderr));
    String::from_utf8(output.stdout.clone()).unwrap()
}

fn realization_rows(text: &str) -> BTreeSet<String> {
    text.lines()
        .filter(|line| line.starts_with("TYPE\t") || line.starts_with("SAME\t"))
        .map(str::to_string)
        .collect()
}

fn expected(name: &str) -> BTreeSet<String> {
    std::fs::read_to_string(fixture(name))
        .unwrap()
        .lines()
        .filter(|line| !line.is_empty())
        .map(str::to_string)
        .collect()
}

fn taxonomy_lines(text: &str) -> Vec<&str> {
    text.lines()
        .filter(|line| !line.starts_with("TYPE\t") && !line.starts_with("SAME\t"))
        .collect()
}

#[test]
fn realize_reports_every_entailed_type_and_equality() {
    for case in CASES {
        let source = fixture(&format!("{case}.ofn"));
        let plain = stdout(&km(&source, &["--lines"]));
        let realized = stdout(&km(&source, &["--lines", "--realize"]));
        assert_eq!(realization_rows(&realized), expected(&format!("{case}.all")), "{case}");
        // The taxonomy part is the plain classification, byte for byte, and
        // the realization rows follow it.
        assert!(realized.starts_with(&plain[..plain.len() - 1]), "{case}: taxonomy prefix differs");
        assert_eq!(taxonomy_lines(&realized), taxonomy_lines(&plain), "{case}");
    }
}

#[test]
fn realize_direct_reports_the_most_specific_types() {
    for case in ["exists_forall", "chain", "functional", "sameas", "cases"] {
        let source = fixture(&format!("{case}.ofn"));
        let realized = stdout(&km(&source, &["--lines", "--realize=direct"]));
        assert_eq!(realization_rows(&realized), expected(&format!("{case}.direct")), "{case}");
    }
}

#[test]
fn inconsistent_abox_reports_inconsistency_without_rows() {
    let realized = stdout(&km(&fixture("inconsistent.ofn"), &["--lines", "--realize"]));
    assert!(realized.starts_with("CONSISTENT 0\n"), "{realized}");
    assert!(realization_rows(&realized).is_empty());
}

#[test]
fn json_realization_adds_only_types_and_same() {
    let source = fixture("sameas.ofn");
    let plain: serde_json::Value = serde_json::from_slice(&km(&source, &[]).stdout).unwrap();
    let output = km(&source, &["--realize"]);
    assert!(output.status.success());
    let mut realized: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    let object = realized.as_object_mut().unwrap();
    let types = object.remove("types").unwrap();
    let same = object.remove("same").unwrap();
    assert_eq!(realized, plain);
    assert!(types.as_array().unwrap().contains(&serde_json::json!(["urn:t#c", "urn:t#D"])));
    assert_eq!(same, serde_json::json!([["urn:t#a", "urn:t#b"], ["urn:t#a", "urn:t#c"], ["urn:t#b", "urn:t#c"]]));
}

#[test]
fn realize_options_are_validated() {
    let source = fixture("sameas.ofn");
    for options in [&["--realize=sometimes"][..], &["--realize", "--json-edges"][..]] {
        let output = km(&source, options);
        assert_eq!(output.status.code(), Some(2), "{options:?}");
        assert!(output.stdout.is_empty());
    }
    let help = km(&source, &["--help"]);
    assert!(String::from_utf8_lossy(&help.stdout).contains("TYPE<TAB>a<TAB>C"));
}

/// The plugin-side reduction: append `I_a ≡ {a}` per individual to the source
/// and classify. `--realize` must give the same rows as reading this answer.
#[test]
fn realize_agrees_with_the_source_level_class_per_individual_reduction() {
    for case in CASES {
        let path = fixture(&format!("{case}.ofn"));
        let text = std::fs::read_to_string(&path).unwrap();
        let individuals: BTreeSet<String> = text
            .split("NamedIndividual(<")
            .skip(1)
            .map(|rest| rest[..rest.find('>').unwrap()].to_string())
            .collect();
        let mut extended = text.trim_end().strip_suffix(')').unwrap().to_string();
        let probe = |a: &str| format!("urn:test:probe:{a}");
        for a in &individuals {
            extended.push_str(&format!(
                "Declaration(Class(<{p}>)) EquivalentClasses(<{p}> ObjectOneOf(<{a}>))\n",
                p = probe(a)
            ));
        }
        extended.push_str(")\n");
        let reduced_path = std::env::temp_dir().join(format!("km-realize-reduction-{}-{case}.ofn", std::process::id()));
        std::fs::write(&reduced_path, extended).unwrap();
        let reduced = stdout(&km(&reduced_path, &["--lines"]));
        std::fs::remove_file(&reduced_path).unwrap();
        let mut rows = BTreeSet::new();
        if reduced.starts_with("CONSISTENT 1") {
            for line in reduced.lines() {
                let fields: Vec<&str> = line.split('\t').collect();
                if fields.len() != 3 || fields[0] != "SUB" {
                    continue;
                }
                let Some(a) = fields[1].strip_prefix("urn:test:probe:") else { continue };
                match fields[2].strip_prefix("urn:test:probe:") {
                    Some(b) if a < b => {
                        rows.insert(format!("SAME\t{a}\t{b}"));
                    }
                    Some(_) => {}
                    None => {
                        rows.insert(format!("TYPE\t{a}\t{}", fields[2]));
                    }
                }
            }
        }
        let realized = stdout(&km(&path, &["--lines", "--realize"]));
        assert_eq!(realization_rows(&realized), rows, "{case}");
    }
}

/// Realization is answered only under the automatic route policy.
#[test]
fn forced_routes_are_refused_without_the_diagnostic_override() {
    let source = fixture("sameas.ofn");
    for route in ["nominals", "cb_plain1"] {
        let output = km(&source, &["--lines", "--realize", "--route", route]);
        assert_eq!(output.status.code(), Some(3), "{route}");
        assert!(output.stdout.is_empty());
        assert!(String::from_utf8_lossy(&output.stderr).contains("realization-safe"));
    }
    let output = km_env(&source, &["--lines", "--realize"], &[("KM_ROUTE", "manual")]);
    assert_eq!(output.status.code(), Some(3));
}

/// Under the diagnostic override, each nominal-complete route either declines
/// (non-zero exit or `DROPPED > 0`) or gives exactly the oracle's rows.
#[test]
fn nominal_routes_give_the_oracle_realization_or_decline() {
    let routes = ["ht_bridge", "certified_nominals", "nominal_ni_abox", "nominals", "ht_full", "certified_card_nominals"];
    let mut answered = 0usize;
    for case in CASES {
        let source = fixture(&format!("{case}.ofn"));
        let oracle = expected(&format!("{case}.all"));
        for route in routes {
            let output = km_env(&source, &["--lines", "--realize", "--route", route], &[("KM_REALIZE_ANY_ROUTE", "1")]);
            if !output.status.success() {
                continue;
            }
            let text = String::from_utf8(output.stdout).unwrap();
            if !text.lines().any(|line| line == "DROPPED 0") {
                continue;
            }
            answered += 1;
            assert_eq!(realization_rows(&text), oracle, "{case} on route {route}");
        }
    }
    assert!(answered >= CASES.len() * 4, "only {answered} route answers");
}

#[test]
fn prefixed_and_rdfxml_individuals_use_the_classification_spelling() {
    let dir = std::env::temp_dir();
    let ofn = dir.join(format!("km-realize-prefixed-{}.ofn", std::process::id()));
    std::fs::write(&ofn, "Prefix(:=<urn:p#>)\nOntology(Declaration(Class(:C)) Declaration(Class(:D)) \
        Declaration(NamedIndividual(:a)) SubClassOf(:C :D) ClassAssertion(:C :a))\n").unwrap();
    let text = stdout(&km(&ofn, &["--lines", "--realize"]));
    std::fs::remove_file(&ofn).unwrap();
    let sub = text.lines().find(|line| line.starts_with("SUB\t")).unwrap().to_string();
    let fields: Vec<&str> = sub.split('\t').collect();
    let individual = if fields[1].starts_with("urn:") { "urn:p#a" } else { ":a" };
    assert_eq!(
        realization_rows(&text),
        [format!("TYPE\t{individual}\t{}", fields[1]), format!("TYPE\t{individual}\t{}", fields[2])]
            .into_iter()
            .collect()
    );

    let rdf = dir.join(format!("km-realize-{}.rdf", std::process::id()));
    std::fs::write(&rdf, r#"<?xml version="1.0"?>
<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"
 xmlns:rdfs="http://www.w3.org/2000/01/rdf-schema#"
 xmlns:owl="http://www.w3.org/2002/07/owl#">
 <owl:Ontology rdf:about="http://example.org/o"/>
 <owl:Class rdf:about="http://example.org/C"><rdfs:subClassOf rdf:resource="http://example.org/D"/></owl:Class>
 <owl:Class rdf:about="http://example.org/D"/>
 <owl:NamedIndividual rdf:about="http://example.org/a"><rdf:type rdf:resource="http://example.org/C"/></owl:NamedIndividual>
 <owl:NamedIndividual rdf:about="http://example.org/b"><owl:sameAs rdf:resource="http://example.org/a"/></owl:NamedIndividual>
</rdf:RDF>"#).unwrap();
    let text = stdout(&km(&rdf, &["--lines", "--realize", "--format", "rdfxml"]));
    std::fs::remove_file(&rdf).unwrap();
    assert_eq!(
        realization_rows(&text),
        [
            "TYPE\thttp://example.org/a\thttp://example.org/C",
            "TYPE\thttp://example.org/a\thttp://example.org/D",
            "TYPE\thttp://example.org/b\thttp://example.org/C",
            "TYPE\thttp://example.org/b\thttp://example.org/D",
            "SAME\thttp://example.org/a\thttp://example.org/b",
        ]
        .into_iter()
        .map(str::to_string)
        .collect()
    );
}

fn realize_source(name: &str, source: &str) -> (String, String) {
    let path = std::env::temp_dir().join(format!("km-realize-{name}-{}.ofn", std::process::id()));
    std::fs::write(&path, source).unwrap();
    let plain = stdout(&km(&path, &["--lines"]));
    let realized = stdout(&km(&path, &["--lines", "--realize"]));
    std::fs::remove_file(&path).unwrap();
    (plain, realized)
}

/// One individual written as `:a` and as its full IRI is one individual: one
/// TYPE row, no SAME row. Names follow classify's spelling rule (a prefixed
/// name becomes the full IRI where both spellings occur).
#[test]
fn mixed_spellings_of_one_individual_are_one_individual() {
    let (plain, realized) = realize_source("mixed", "Prefix(:=<http://x/o#>)\nOntology(<http://x/o>\n\
        Declaration(Class(:C)) Declaration(Class(:D)) Declaration(NamedIndividual(:a))\n\
        SubClassOf(:C :D)\nClassAssertion(:C <http://x/o#a>)\nClassAssertion(:C :a)\n)\n");
    let sub = plain.lines().find(|line| line.starts_with("SUB\t")).unwrap();
    let fields: Vec<&str> = sub.split('\t').collect();
    assert_eq!(
        realization_rows(&realized),
        [format!("TYPE\thttp://x/o#a\t{}", fields[1]), format!("TYPE\thttp://x/o#a\t{}", fields[2])]
            .into_iter()
            .collect()
    );
    assert_eq!(taxonomy_lines(&realized), taxonomy_lines(&plain));
}

#[test]
fn mixed_spelling_same_individual_reports_one_pair() {
    let (plain, realized) = realize_source("mixed-same", "Prefix(:=<http://x/o#>)\nOntology(<http://x/o>\n\
        Declaration(Class(<http://x/o#C>)) Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))\n\
        SameIndividual(:a <http://x/o#b>)\nClassAssertion(:C :b)\n)\n");
    assert_eq!(
        realization_rows(&realized),
        ["TYPE\t:a\thttp://x/o#C", "TYPE\thttp://x/o#b\thttp://x/o#C", "SAME\t:a\thttp://x/o#b"]
            .into_iter()
            .map(str::to_string)
            .collect()
    );
    assert_eq!(taxonomy_lines(&realized), taxonomy_lines(&plain));
}
