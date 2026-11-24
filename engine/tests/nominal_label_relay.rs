//! A label of a nominal concept on an individual, derived in a context under
//! its own core and read by a successor of that context (docs/NOMINALS-CB.md
//! 14.4). `E ⊑ ∃s.{o}` and `E ⊑ ∀s.{a}` make `o = a` under `E`, which the
//! `E` context records as the label `__nom__a(o)`. Its successor `Z ⊑ ∃r.{o}`
//! reads it through `Z ⊓ ∃r.{a} ⊑ W`, so `E ⊑ ∃t.W` (HermiT, consistency
//! test). Offering nominal labels over the grounded edges only (a prototype
//! that made the f9001 probes and x9416_0075 fast) misses it on the forced
//! nominal routes; the every-edge offers, demand-driven or not, find it.
use std::path::{Path, PathBuf};
use std::process::Command;

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/nominal_label_relay").join(name)
}

fn subsumptions(path: &Path, route: Option<&str>, extra: &[(&str, &str)]) -> Vec<String> {
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
    for (key, value) in extra {
        command.env(key, value);
    }
    let output = command.arg("classify").arg("--lines").arg(path).output().unwrap();
    assert!(output.status.success(), "km failed on {} {route:?}", path.display());
    String::from_utf8_lossy(&output.stdout)
        .lines()
        .filter(|line| line.starts_with("SUB"))
        .map(|line| line.split_whitespace().collect::<Vec<_>>().join(" "))
        .collect()
}

#[test]
fn a_conditional_nominal_label_reaches_its_reader() {
    let path = fixture("conditional_nominal_label.ofn");
    for route in [None, Some("nominals"), Some("certified_nominals")] {
        for demand in ["1", "0"] {
            let subs = subsumptions(&path, route, &[("KM_RSUCC_DEMAND", demand)]);
            assert!(
                subs.iter().any(|line| line == "SUB :E :Q"),
                "E ⊑ Q missing on {route:?} with KM_RSUCC_DEMAND={demand}: {subs:?}"
            );
        }
    }
}
