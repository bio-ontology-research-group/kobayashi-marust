//! Regression for dependency sets lost across node merges in the hypertableau.
//!
//! A fact moved from a merged node onto its survivor holds only under the
//! dependency set of that merge. Dropping the set gave a nominal clash an empty
//! dependency set, so backjumping skipped the remaining disjuncts and reported a
//! satisfiable class as unsatisfiable (first seen on ore_ont_5964).
use std::path::PathBuf;
use std::process::Command;

fn data(name: &str) -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data/ht_merge_dependency").join(name)
}

fn classify(path: &PathBuf, route: &str, isolated: bool, threads: &str) -> Option<serde_json::Value> {
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    command.args(["classify", "--route", route]).arg(path).env("KM_HT_PAR", threads);
    if isolated {
        command.env("KM_NO_INPROC_HT", "1");
    }
    let output = command.output().unwrap();
    if !output.status.success() {
        // A route may decline an input it does not cover. It must never answer wrongly.
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("unsupported"), "{route}: {stderr}");
        return None;
    }
    Some(serde_json::from_slice(&output.stdout).unwrap())
}

fn pairs(result: &serde_json::Value) -> Vec<(String, String)> {
    let mut pairs: Vec<(String, String)> = result["subsumptions"]
        .as_array()
        .unwrap()
        .iter()
        .map(|pair| (pair[0].as_str().unwrap().to_owned(), pair[1].as_str().unwrap().to_owned()))
        .collect();
    pairs.sort();
    pairs
}

#[test]
fn value_partition_classes_stay_satisfiable() {
    let wine = "http://www.ifomis.org/bfo/1.1#";
    let expected = vec![
        (format!("{wine}Anjou"), format!("{wine}Wine")),
        (format!("{wine}Burgundy"), format!("{wine}Wine")),
    ];
    let mut answered = 0;
    for route in ["auto", "ht_general", "ht_card", "ht_shoq", "production_all", "nominals"] {
        for isolated in [false, true] {
            for threads in ["1", "4"] {
                let Some(result) = classify(&data("wine-sugar.owl"), route, isolated, threads) else {
                    continue;
                };
                answered += 1;
                let context = format!("route={route} isolated={isolated} threads={threads}");
                assert_eq!(result["consistent"], true, "{context}");
                assert_eq!(result["unsatisfiable"].as_array().unwrap().len(), 0, "{context}");
                assert_eq!(result["dropped"], 0, "{context}");
                assert_eq!(pairs(&result), expected, "{context}");
            }
        }
    }
    assert!(answered >= 8, "too few routes answered: {answered}");
}

#[test]
fn two_nominal_exact_cardinality_stays_satisfiable() {
    let mut answered = 0;
    for route in ["auto", "ht_general", "ht_card", "ht_shoq", "production_all", "nominals"] {
        for isolated in [false, true] {
            let Some(result) = classify(&data("tiny2.owl"), route, isolated, "1") else {
                continue;
            };
            answered += 1;
            let context = format!("route={route} isolated={isolated}");
            assert_eq!(result["consistent"], true, "{context}");
            assert_eq!(result["unsatisfiable"].as_array().unwrap().len(), 0, "{context}");
            assert_eq!(result["dropped"], 0, "{context}");
        }
    }
    assert!(answered >= 4, "too few routes answered: {answered}");
}
