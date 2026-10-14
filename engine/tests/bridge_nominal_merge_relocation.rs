//! Regression (fuzz case 1002). `Thing <= some r.{a}` with
//! InverseFunctional(r) collapses every model to one element, so in the
//! cases below every successor is that element.
//!
//! * `stale_current_node`: a clash aborted the processing of a node, the
//!   backtrack restored the graph but left it as the "current" node, and a
//!   later merge's concepts on it were never queued (A0 <= A6 was lost).
//! * `nominal_link_relocation`: merge phase 5 moved only the ancestor's links,
//!   so a nominal's at-most never saw the merge target of its r-predecessors
//!   (A4 was not found unsatisfiable).
//! * `merged_root_read_off`: the read-off read the merged-away root's stale
//!   label instead of its merge representative.
use std::process::Command;

const HEAD: &str = "Prefix(:=<http://f/>)
Prefix(owl:=<http://www.w3.org/2002/07/owl#>)
Ontology(<http://f/o>
Declaration(Class(:A0)) Declaration(Class(:A3)) Declaration(Class(:A4))
Declaration(Class(:A5)) Declaration(Class(:A6))
Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:s)) Declaration(ObjectProperty(:t))
Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:c))
InverseFunctionalObjectProperty(:r)
SubClassOf(owl:Thing ObjectSomeValuesFrom(:r ObjectOneOf(:a)))
ClassAssertion(ObjectAllValuesFrom(ObjectInverseOf(:r) ObjectAllValuesFrom(ObjectInverseOf(:t) :A6)) :c)
";

fn classify(name: &str, axioms: &str, route: &str) -> serde_json::Value {
    let dir = std::env::temp_dir().join(format!("km-bridge-ni-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("{name}-{route}.ofn"));
    std::fs::write(&path, format!("{HEAD}{axioms}\n)\n")).unwrap();
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars() {
        if key.starts_with("KM_") {
            command.env_remove(key);
        }
    }
    let result = command
        .arg("classify")
        .arg(&path)
        .env("KM_ROUTE", route)
        .env("KM_THREADS", "1")
        .env("KM_HT_DDB", "1")
        .env("KM_HT_NATIVE_FULL", "1")
        .env("KM_CACHE_CONFORMANCE", "1")
        .env("KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE", "1")
        .env("KM_FAST_IRI_GRAMMAR", "1")
        .output()
        .expect("run km classification");
    assert!(result.status.success(), "{name}/{route}: {}", String::from_utf8_lossy(&result.stderr));
    serde_json::from_slice(&result.stdout).unwrap()
}

/// The answer as (sorted subsumptions without unsatisfiable subjects,
/// sorted unsatisfiable classes); HermiT's answer is the expectation.
fn answer(value: &serde_json::Value) -> (Vec<(String, String)>, Vec<String>) {
    assert_eq!(value["consistent"], true);
    let unsat: Vec<String> = value["unsatisfiable"]
        .as_array()
        .unwrap()
        .iter()
        .map(|x| x.as_str().unwrap().to_string())
        .collect();
    let mut subs: Vec<(String, String)> = value["subsumptions"]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| (p[0].as_str().unwrap().to_string(), p[1].as_str().unwrap().to_string()))
        .filter(|(sub, _)| !unsat.contains(sub))
        .collect();
    subs.sort();
    let mut unsat = unsat;
    unsat.sort();
    (subs, unsat)
}

fn pairs(list: &[(&str, &str)]) -> Vec<(String, String)> {
    list.iter().map(|(a, b)| (a.to_string(), b.to_string())).collect()
}

#[test]
fn stale_current_node_after_backtrack() {
    for route in ["ht_bridge", "auto"] {
        let got = answer(&classify("stale", "SubClassOf(:A0 ObjectSomeValuesFrom(:t :A6))", route));
        assert_eq!(got, (pairs(&[(":A0", ":A6")]), vec![]), "{route}");
    }
}

#[test]
fn merged_successor_reaches_nominal_universal() {
    for route in ["ht_bridge", "auto"] {
        let got = answer(&classify("succ", "SubClassOf(:A5 ObjectSomeValuesFrom(:t :A3))", route));
        assert_eq!(got, (pairs(&[(":A5", ":A3"), (":A5", ":A6")]), vec![]), "{route}");
    }
}

#[test]
fn nominal_link_relocation_finds_inverse_functional_clash() {
    let axioms = "SubClassOf(:A6 ObjectSomeValuesFrom(:t ObjectComplementOf(:A4)))
SubClassOf(:A4 ObjectSomeValuesFrom(:s :A0))
SubClassOf(:A0 ObjectSomeValuesFrom(:t :A6))";
    for route in ["ht_bridge", "auto"] {
        let got = answer(&classify("relocate", axioms, route));
        assert_eq!(got, (pairs(&[(":A0", ":A6")]), vec![":A4".to_string()]), "{route}");
    }
}
