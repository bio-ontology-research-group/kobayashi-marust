//! A successor of an individual that reads the individual through an inverse
//! role. For `a : ∃t.C`, `∃t⁻.K ⊑ E` (or `∃t⁻.{a} ⊑ E`), `K(a)` and
//! `E ⊓ C ⊑ ⊥` the ontology is inconsistent (HermiT); the nominal CB engine
//! offers no label of `a` to its successor `f(a)` and answered consistent on
//! `certified_nominals` and `nominals`, and on the automatic route through a
//! fall-through after the bridge declined. Every route must now answer
//! inconsistent or decline; the automatic route must answer.
use std::path::{Path, PathBuf};
use std::process::Command;

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/nominal_cb_predecessor").join(name)
}

/// `Some(first line)` on success, `None` when the route declines.
fn first_line(path: &Path, route: Option<&str>) -> Option<String> {
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars() {
        if key.starts_with("KM_") {
            command.env_remove(key);
        }
    }
    command.env("KM_THREADS", "1");
    if let Some(route) = route {
        command.env("KM_ROUTE", route);
    }
    let output = command.arg("classify").arg("--lines").arg(path).output().unwrap();
    output.status.success().then(|| String::from_utf8_lossy(&output.stdout).lines().next().unwrap_or("").to_string())
}

const CASES: [&str; 4] = [
    "has-value-inverse.ofn",
    "has-value-inverse-negative-data.ofn",
    "one-of-successor.ofn",
    "inverse-label-at-individual.ofn",
];

#[test]
fn every_route_answers_inconsistent_or_declines() {
    for case in CASES {
        for route in ["certified_nominals", "nominals", "certified_card_nominals", "ht_bridge", "cb_plain1",
                      "production_all", "lean", "default"] {
            if let Some(line) = first_line(&fixture(case), Some(route)) {
                assert_eq!(line, "CONSISTENT 0", "{case} on {route}");
            }
        }
    }
}

#[test]
fn the_automatic_route_answers_inconsistent() {
    for case in CASES {
        assert_eq!(first_line(&fixture(case), None).as_deref(), Some("CONSISTENT 0"), "{case}");
    }
}
