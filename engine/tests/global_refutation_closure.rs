//! Missed inconsistencies on the CB engine after the one-shot stop at a
//! global refutation (docs/PER-CONTEXT-ORDERING.md section 12). Expected
//! answers are HermiT 1.4.3.456's: every fixture is inconsistent.
//!
//! * `alchiq_621`, `alchiq_1014`, `alchiq_1022`: seeds 621 (the 700 ALCHIQ
//!   seeds) and 1014, 1022 (the fresh `gen_alc.py` seeds) of the 2026-10-29
//!   bridge seed set, wrong on the automatic route from b88c6253 on.
//! * `alchiq_*_min`: the same seeds reduced axiom by axiom while the
//!   development binary 0e1bd99a still answered `CONSISTENT 1`.
//!
//! In each, the ontology facts alone refute `⊤` (`⊤ ⊑ B` with `B`
//! unsatisfiable, or `C ≡ ¬(C ⊓ B)` with `⊤ ⊑ B`). The first query context
//! builds the shared root closure on a throwaway empty-core root context,
//! which derives the empty clause and sets the global-refutation flag; the
//! run then stopped before it created the `⊤` context, and
//! `Engine::inconsistent` scanned only the contexts that remain, so it
//! answered consistent. It now reads the flag.
use std::process::Command;

fn consistent(path: &str, extra: &[(&str, &str)]) -> bool {
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars_os() {
        if key.to_string_lossy().starts_with("KM_") {
            command.env_remove(key);
        }
    }
    for (key, value) in extra {
        command.env(key, value);
    }
    let output = command.args(["classify", "--lines", path]).output().unwrap();
    assert!(output.status.success(), "km failed on {path} {extra:?}");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let first = stdout.lines().next().unwrap_or_default().to_string();
    assert!(first.starts_with("CONSISTENT "), "{path} {extra:?}: {first}");
    first == "CONSISTENT 1"
}

fn fixture(name: &str) -> String {
    format!("{}/tests/fixtures/global_refutation_closure/{name}.ofn", env!("CARGO_MANIFEST_DIR"))
}

const NAMES: &[&str] = &[
    "alchiq_621",
    "alchiq_1014",
    "alchiq_1022",
    "alchiq_621_min",
    "alchiq_1014_min",
    "alchiq_1022_min",
];

#[test]
fn automatic_route_reports_the_inconsistency() {
    for name in NAMES {
        for threads in ["1", "4"] {
            assert!(!consistent(&fixture(name), &[("KM_THREADS", threads)]), "{name} threads={threads}");
        }
    }
}

/// The CB engine worker alone, single-threaded and parallel: the stopped run
/// must still report `inconsistent`.
#[test]
fn engine_worker_reports_the_inconsistency() {
    for name in NAMES {
        let clauses = Command::new(env!("CARGO_BIN_EXE_km"))
            .args(["ofn", &fixture(name)])
            .output()
            .unwrap();
        assert!(clauses.status.success(), "ofn failed on {name}");
        for threads in ["1", "4"] {
            let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
            for (key, _) in std::env::vars_os() {
                if key.to_string_lossy().starts_with("KM_") {
                    command.env_remove(key);
                }
            }
            command.env("KM_THREADS", threads).arg("engine");
            command.stdin(std::process::Stdio::piped()).stdout(std::process::Stdio::piped());
            let mut child = command.spawn().unwrap();
            {
                use std::io::Write;
                child.stdin.take().unwrap().write_all(&clauses.stdout).unwrap();
            }
            let output = child.wait_with_output().unwrap();
            assert!(output.status.success(), "engine failed on {name}");
            let stdout = String::from_utf8_lossy(&output.stdout);
            assert!(stdout.contains("\"inconsistent\":true"), "{name} threads={threads}: {stdout}");
        }
    }
}
