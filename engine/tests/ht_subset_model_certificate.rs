//! Lean checking of subset-blocked production terminals of the native
//! hypertableau (docs/HYBRID-CB-HT.md section 9, "Lean coverage"). With
//! `KM_HT_SUBSET_MODEL_CERT` every SAT terminal of blocking modes 1 and 5 is
//! written as a `WireSubsetUnravelling`; with `KM_HT_SUBSET_MODEL_CHECKER`
//! the worker runs `ht-subset-unravelling-check` on it and gives no verdict
//! when Lean rejects it. `KM_HT_INCRBLOCK2_CHECK=1` also compares every
//! incremental blocking pass with the full scan.
//!
//! The checker path comes from `KM_HT_TEST_SUBSET_MODEL_CHECKER`
//! (`lean/run-ht-certification-gate.sh` sets it); without it the tests skip
//! unless `KM_REQUIRE_LEAN_CHECKERS` is set.
use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

static NEXT: AtomicUsize = AtomicUsize::new(0);

fn checker() -> Option<PathBuf> {
    match std::env::var_os("KM_HT_TEST_SUBSET_MODEL_CHECKER") {
        Some(path) => Some(path.into()),
        None => {
            assert!(
                std::env::var_os("KM_REQUIRE_LEAN_CHECKERS").is_none(),
                "KM_HT_TEST_SUBSET_MODEL_CHECKER is required"
            );
            eprintln!("skipping: KM_HT_TEST_SUBSET_MODEL_CHECKER is unset");
            None
        }
    }
}

const HEADER: &str = "Prefix(:=<http://example.org/g#>)\n\
    Prefix(owl:=<http://www.w3.org/2002/07/owl#>)\n\
    Ontology(<http://example.org/g>\n\
    Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C)) Declaration(Class(:D))\n\
    Declaration(Class(:E)) Declaration(Class(:Q1)) Declaration(Class(:Q2)) Declaration(Class(:Q3))\n\
    Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:s)) Declaration(ObjectProperty(:t))\n";

/// Counts of the `KM_HT_SUBSET_MODEL_CERT` lines of one run.
#[derive(Debug, Default)]
struct Terminals {
    accepted: usize,
    accepted_with_folds: usize,
    rejected: usize,
    not_emitted: usize,
}

fn run(axioms: &str, route: &str, checker: Option<&PathBuf>) -> (String, Terminals) {
    let id = NEXT.fetch_add(1, Ordering::Relaxed);
    let base = std::env::temp_dir().join(format!("km-ht-subset-model-{}-{id}", std::process::id()));
    let ontology = base.with_extension("ofn");
    std::fs::write(&ontology, format!("{HEADER}{axioms}\n)\n")).unwrap();
    let dir = base.with_extension("certs");
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars_os() {
        if key.to_string_lossy().starts_with("KM_") {
            command.env_remove(key);
        }
    }
    command.env("KM_ROUTE", route).args(["classify", "--lines"]).arg(&ontology);
    if let Some(checker) = checker {
        command
            .env("KM_HT_SUBSET_MODEL_CERT", &dir)
            .env("KM_HT_SUBSET_MODEL_CHECKER", checker)
            .env("KM_HT_INCRBLOCK2_CHECK", "1");
    }
    let output = command.output().unwrap();
    let _ = std::fs::remove_file(&ontology);
    if std::env::var_os("KM_HT_TEST_KEEP_CERT").is_none() {
        let _ = std::fs::remove_dir_all(&dir);
    }
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    assert!(output.status.success(), "km failed on {route}: {stderr}");
    let mut terminals = Terminals::default();
    for line in stderr.lines().filter(|line| line.starts_with("KM_HT_SUBSET_MODEL_CERT ")) {
        if line.ends_with(" accepted") {
            terminals.accepted += 1;
            if !line.contains(" folds=0 ") {
                terminals.accepted_with_folds += 1;
            }
        } else if line.ends_with(" rejected") {
            terminals.rejected += 1;
        } else if line.contains("not emitted") {
            terminals.not_emitted += 1;
        }
    }
    let mut lines: Vec<String> = String::from_utf8(output.stdout).unwrap().lines().map(str::to_string).collect();
    lines.sort();
    (lines.join("\n"), terminals)
}

fn assert_checked(axioms: &str) -> Terminals {
    let Some(checker) = checker() else { return Terminals::default() };
    let (checked, terminals) = run(axioms, "ht_general", Some(&checker));
    let (plain, _) = run(axioms, "ht_general", None);
    assert_eq!(checked, plain, "certificate checking changed the answer");
    assert_eq!(terminals.rejected, 0, "Lean rejected a terminal: {terminals:?}");
    assert_eq!(terminals.not_emitted, 0, "a terminal had no certificate: {terminals:?}");
    eprintln!("{terminals:?}");
    terminals
}

/// Seed 507 of tests/ht_subset_blocking.rs: consistent, with checked subset
/// pairs (`∃s.A` and `∃s.B` recognitions read a neighbour literal).
#[test]
fn seed_507_subset_blocked_terminals_are_lean_checked() {
    let terminals = assert_checked(
        "EquivalentClasses(:B ObjectUnionOf(ObjectSomeValuesFrom(:s :A) ObjectComplementOf(:B)))\n\
         DisjointClasses(ObjectUnionOf(ObjectSomeValuesFrom(:s :B) ObjectComplementOf(:B)) :D)\n\
         EquivalentClasses(:Q3 ObjectIntersectionOf(ObjectIntersectionOf(:D :A) ObjectMaxCardinality(2 :t :C)))",
    );
    if checker().is_some() {
        assert!(terminals.accepted > 0, "{terminals:?}");
    }
}

/// Seed 639 of tests/ht_subset_blocking.rs: `C ⊑ ∃r.A`, `≥1 r.B ⊑ B`,
/// `⊤ ⊑ ∃s.D`; every model is infinite without blocking, so some accepted
/// terminal carries a blocking pair.
#[test]
fn seed_639_subset_blocked_terminals_are_lean_checked() {
    let terminals = assert_checked(
        "EquivalentClasses(:D :C)\n\
         SubClassOf(ObjectMinCardinality(1 :r :B) :B)\n\
         SubClassOf(:C ObjectSomeValuesFrom(:r :A))\n\
         DisjointClasses(ObjectComplementOf(ObjectIntersectionOf(:A :B)) :A)\n\
         SubClassOf(owl:Thing ObjectSomeValuesFrom(:s :D))\n\
         EquivalentClasses(:Q3 ObjectUnionOf(:C ObjectComplementOf(ObjectUnionOf(:C ObjectComplementOf(:B)))))",
    );
    if checker().is_some() {
        assert!(terminals.accepted_with_folds > 0, "{terminals:?}");
    }
}
