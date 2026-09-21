//! A class equivalent to a complement forces a case split on every node.
//!
//! The general hypertableau is not complete for either clause form yet, so the
//! literal movement is opt-in (`KM_HT_MOVE_SIGNED_LITERALS`). Both known cases
//! are pinned here: `top6.owl` needs the movement, `min778.owl` needs the signed
//! form. A real fix must make both pass in ONE configuration.
//!
//! `Tan ≡ ¬Int`, `Int ⊑ Thing`, `Tan ⊑ Temp ⊑ Thing` make `Thing` equivalent to
//! owl:Thing, so every class is below it, including classes no axiom connects
//! to the split (first seen on ore_ont_12566 with the general hypertableau).
use std::process::Command;

#[test]
fn complement_equivalence_reaches_unrelated_classes() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data/ht_signed_literals/top6.owl");
    let mut answered = 0;
    for route in ["auto", "ht_general", "ht_bridge", "production_all", "nominals"] {
        for isolated in [false, true] {
            let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
            command.args(["classify", "--route", route]).arg(&path).env("KM_HT_MOVE_SIGNED_LITERALS", "1");
            if isolated {
                command.env("KM_NO_INPROC_HT", "1");
            }
            let output = command.output().unwrap();
            if !output.status.success() {
                let stderr = String::from_utf8_lossy(&output.stderr);
                assert!(stderr.contains("unsupported"), "{route}: {stderr}");
                continue;
            }
            answered += 1;
            let result: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
            assert_eq!(result["consistent"], true, "{route}");
            assert_eq!(result["dropped"], 0, "{route}");
            assert_eq!(result["unsatisfiable"].as_array().unwrap().len(), 0, "{route}");
            let subs = result["subsumptions"].as_array().unwrap();
            for class in ["Z", "News", "Comp", "Int", "Q", "Tan", "Temp"] {
                let sub = format!("http://e/{class}");
                assert!(
                    subs.iter().any(|pair| pair[0] == sub.as_str() && pair[1] == "http://e/Thing"),
                    "route={route} isolated={isolated}: {class} must be below Thing"
                );
            }
        }
    }
    assert!(answered >= 6, "too few routes answered: {answered}");
}

/// Reduced from ore_ont_778 (HermiT: AfricanElephant ⊑ OmnivoreAnimal). The
/// default, signed form must keep deriving it.
#[test]
fn nested_partition_subsumption_survives_by_default() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data/ht_signed_literals/min778.owl");
    let animals = "http://www.imbi.uni-freiburg.de/ontologies/2011/Animals.owl#";
    for route in ["auto", "ht_general"] {
        let output = Command::new(env!("CARGO_BIN_EXE_km"))
            .args(["classify", "--route", route])
            .arg(&path)
            .env_remove("KM_HT_MOVE_SIGNED_LITERALS")
            .output()
            .unwrap();
        assert!(output.status.success(), "{route}: {}", String::from_utf8_lossy(&output.stderr));
        let result: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(result["consistent"], true, "{route}");
        let sub = format!("{animals}AfricanElephant");
        let sup = format!("{animals}OmnivoreAnimal");
        assert!(
            result["subsumptions"].as_array().unwrap().iter().any(|pair| pair[0] == sub.as_str() && pair[1] == sup.as_str()),
            "{route}: AfricanElephant must be below OmnivoreAnimal"
        );
    }
}
