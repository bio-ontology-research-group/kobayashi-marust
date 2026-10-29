//! A sequential classification must not inherit the cancellation a completed
//! race left behind.
//!
//! The test spawns reasoner workers, so it needs the real `km` binary as the
//! worker program (inside the library's test process `current_exe` is the test
//! harness, which cannot act as a worker). The orchestrator also mutates the
//! process-global `KM_*` route environment while it classifies; in the library
//! test process that leaks into every other test, so this test lives in its
//! own binary.

use kobayashi_marust::orchestrate::tmpfile::TempPath;
use kobayashi_marust::orchestrate::{self, engine_run, Config};

#[test]
fn sequential_classification_does_not_inherit_a_completed_race_cancellation() {
    let file = TempPath::new("-sequential-cancellation.ofn");
    std::fs::write(
        file.path(),
        "Ontology(Declaration(Class(<urn:A>)) Declaration(Class(<urn:B>)) SubClassOf(<urn:A> <urn:B>))",
    )
    .unwrap();
    let mut cfg = Config::from_env();
    cfg.self_exe = env!("CARGO_BIN_EXE_km").into();
    cfg.elc = false;
    cfg.elc_portfolio = false;
    cfg.ht_race = false;
    cfg.tab_race = false;
    let expected = orchestrate::classify(&cfg, file.path()).unwrap();
    engine_run::cancel_and_kill_engines();
    let actual = orchestrate::classify(&cfg, file.path()).unwrap();
    assert_eq!(actual, expected);
    assert!(actual.consistent);
    assert!(actual
        .subsumptions
        .iter()
        .any(|[sub, sup]| sub == "urn:A" && sup == "urn:B"));
}
