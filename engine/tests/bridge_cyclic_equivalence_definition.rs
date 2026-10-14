//! Regression (fuzz s1798). A CCEQ definition is unfolded lazily
//! (`A -> D`, `not A -> not D`, no reverse TOP GCI). That is complete only
//! when `D` does not reach `A`: for `A == not A` a node carrying neither `A`
//! nor `not A` is never forced to choose, so the inconsistency was missed and
//! the bridge reported a consistent ontology with `A` unsatisfiable.
//! Self-reaching definitions keep both inclusions. Expectations are HermiT's.
use std::process::Command;

const HEAD: &str = "Prefix(:=<http://f/>)
Prefix(owl:=<http://www.w3.org/2002/07/owl#>)
Ontology(<http://f/o>
Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C))
";

fn classify(name: &str, axioms: &str, route: &str) -> serde_json::Value {
    let dir = std::env::temp_dir().join(format!("km-bridge-cyclic-eq-{}", std::process::id()));
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

#[test]
fn self_complement_definition_is_inconsistent() {
    for axioms in [
        "EquivalentClasses(:A ObjectComplementOf(:A))",
        "EquivalentClasses(:A ObjectUnionOf(:C ObjectComplementOf(:A))) SubClassOf(:C owl:Nothing)",
        "EquivalentClasses(:A ObjectComplementOf(:A)) SubClassOf(:B :C)",
    ] {
        for route in ["ht_bridge", "auto"] {
            let answer = classify("inconsistent", axioms, route);
            assert_eq!(answer["consistent"], false, "{route}: {axioms}: {answer}");
        }
    }
}

#[test]
fn self_reaching_definition_keeps_the_reverse_inclusion() {
    // A == C and not A: A is unsatisfiable, and so is C (C and not A <= A).
    for route in ["ht_bridge", "auto"] {
        let answer = classify("reverse", "EquivalentClasses(:A ObjectIntersectionOf(:C ObjectComplementOf(:A)))", route);
        assert_eq!(answer["consistent"], true);
        let mut unsat: Vec<&str> = answer["unsatisfiable"].as_array().unwrap().iter().map(|x| x.as_str().unwrap()).collect();
        unsat.sort();
        assert_eq!(unsat, vec![":A", ":C"], "{route}: {answer}");
    }
}
