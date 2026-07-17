//! End-to-end restoration guard for role-chain domain recognition
//! (`KM_CHAIN_DOMAIN`, default ON). This is the mechanism that recovers the
//! historical exact closure of ORE ontology 11745: a *pure-domain* consumer
//! `T(x,y) → D(x)` of a chain target `R∘S⊑T` is only visible after
//! `domain_range_clauses` are built, so `augment`'s pass-1 chain encodings
//! miss it and the unsatisfiability of `GO_0008046` goes undetected — scored
//! unsound against gold (see `docs/HARD-RESIDUAL-AUDIT.md`, `CHANGELOG.md`
//! "Chain-domain recognition validated corpus-wide; now DEFAULT ON").
//!
//! The clause-level unit tests in `src/frontend/preprocess.rs`
//! (`domain_consumer_chain_recognition`,
//! `domain_consumer_transitive_chain_recognition`) verify the recognition
//! *builder* in isolation. They do NOT verify that the pass is actually wired
//! into `classify` and enabled by default — which is exactly the failure mode
//! that left 11745 unsound in every frozen-matrix benchmark binary while the
//! source fix was present. This suite closes that gap end to end.
//!
//! The fixture `chain_domain_unsat.ofn` is the HermiT-confirmed reduced witness
//! (a copy of `oracle/ontologies/11745_unsat_core.ofn`): a probe individual is
//! asserted to be a `GO_0008046`, so the ontology is inconsistent iff that
//! class is recognised unsatisfiable.

use std::path::Path;
use std::process::{Command, Output, Stdio};
use std::time::{Duration, Instant};

fn fixture(name: &str) -> String {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures")
        .join(name)
        .to_string_lossy()
        .into_owned()
}

/// Run `km classify` with a scrubbed `KM_*` environment (so the test observes
/// the DEFAULT routing contract, not the caller's env), optionally forcing one
/// extra variable, under a hard wall-clock bound.
fn classify(extra_env: &[(&str, &str)], ontology: &str) -> Output {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_km"));
    cmd.arg("classify").arg(ontology);
    for (key, _) in std::env::vars() {
        if key.starts_with("KM_") {
            cmd.env_remove(&key);
        }
    }
    for (key, val) in extra_env {
        cmd.env(key, val);
    }
    cmd.stdin(Stdio::null());
    cmd.stdout(Stdio::piped());
    cmd.stderr(Stdio::piped());
    let mut child = cmd.spawn().expect("spawn km classify");
    let deadline = Instant::now() + Duration::from_secs(120);
    loop {
        match child.try_wait().expect("poll km classify") {
            Some(_) => break,
            None if Instant::now() >= deadline => {
                let _ = child.kill();
                let _ = child.wait();
                panic!("km classify exceeded 120 s on the chain-domain witness");
            }
            None => std::thread::sleep(Duration::from_millis(50)),
        }
    }
    child
        .wait_with_output()
        .expect("collect km classify output")
}

fn json_of(out: &Output) -> serde_json::Value {
    assert!(
        out.status.success(),
        "km classify failed: status={:?} stderr={}",
        out.status,
        String::from_utf8_lossy(&out.stderr)
    );
    serde_json::from_slice(&out.stdout).expect("classification JSON")
}

#[test]
fn chain_domain_recognition_is_default_on() {
    // Restoration invariant: with the default environment the witness must be
    // inconsistent (GO_0008046 unsatisfiable). A regression that unwires the
    // pass or silently flips its default OFF turns this back to `consistent`,
    // reintroducing the 11745 unsoundness this test exists to catch.
    let out = classify(&[], &fixture("chain_domain_unsat.ofn"));
    let stderr = String::from_utf8_lossy(&out.stderr).into_owned();
    let v = json_of(&out);
    assert_eq!(
        v["consistent"], false,
        "chain-domain recognition regressed: the 11745 witness is no longer \
         inconsistent by default (stderr: {stderr})"
    );
}

#[test]
fn chain_domain_opt_out_reproduces_the_historical_gap() {
    // Contract of the A/B opt-out and proof that the pass is load-bearing:
    // WITHOUT the recognition the chain feeding the domain restriction is
    // never composed, the clash is missed, and the witness looks consistent.
    // This is the exact under-detection documented for the pre-fix binaries.
    let out = classify(&[("KM_NO_CHAIN_DOMAIN", "1")], &fixture("chain_domain_unsat.ofn"));
    let stderr = String::from_utf8_lossy(&out.stderr).into_owned();
    let v = json_of(&out);
    assert_eq!(
        v["consistent"], true,
        "KM_NO_CHAIN_DOMAIN should reproduce the historical under-detection \
         (consistent witness); if this now fails, some OTHER mechanism closes \
         the clash and the opt-out no longer isolates chain-domain (stderr: {stderr})"
    );
}
