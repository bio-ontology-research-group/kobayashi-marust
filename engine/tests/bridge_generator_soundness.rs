//! Regressions from the nominal-free ALCHIQ generator (v1.5.4). Every
//! fixture in `fixtures/bridge_generator/` went to the Konclude-port bridge
//! on the automatic route and got a wrong answer there. Each `.hermit.json`
//! holds HermiT 1.4's answer for the matching `.ofn`.
//!
//! - `min67_atmost0_definition`, `min_atmost1_definition`: a negated
//!   qualified at-most `not(<=n s.A)` generates `A`-successors, but the
//!   successor saturation lookups used the polarity of `not A` and expanded
//!   the new successor from the wrong saturation node. Pair probes clashed and
//!   the bridge published `A <= Q1` for `Q1 == <=n s.A`.
//! - `min_atleast0_gci`, `min_atleast0_nested`: `>=0 s.C` is TOP, but the
//!   partial absorption gated `SubClassOf(>=0 s.C, C)` on an s-edge, so
//!   `TOP <= C` was lost (missed subsumptions and missed inconsistencies).
//! - `min_copy_successor_insufficient`: a saturation node that copies the
//!   TOP node had its own disjunction resolved but kept an unresolved
//!   successor. The successor's INSUFFICIENT flag stopped at the TOP node,
//!   which was already insufficient for its own reason, so the copy was
//!   certified with a label that lacked `Q1 == exists s.A` (missed
//!   subsumptions).
//! - `clause_*`: incompleteness of the trigger-absorbed clause translation
//!   (`KM_NO_SOURCE_TBOX`). The bridge resolves frontend definer markers to
//!   native concepts, but the trigger-less, guarded, and number-restriction
//!   encoders still emitted the marker atoms, which then had no definition.
//!   `clause_or_definer_fallback` loses `C <= B` from `B == not D or C`
//!   (a non-absorbable definer in a clause body); `clause_top_conjunction`
//!   and `clause_top_conjunction_inconsistent` lose a TOP fact whose head is
//!   a definer (missed subsumptions, a missed inconsistency);
//!   `clause_inverse_exists_negated_filler` loses `C` unsatisfiable through
//!   guarded clauses over `exists inverse(r).not D` definers.
//! - `seedN`: the generator seeds that were wrong before these fixes.
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::Command;

type Answer = (bool, BTreeSet<(String, String)>, BTreeSet<String>);

fn names(value: &serde_json::Value) -> Vec<String> {
    value
        .as_array()
        .unwrap()
        .iter()
        .map(|name| name.as_str().unwrap().trim_start_matches(':').to_string())
        .collect()
}

/// Consistency, the subsumptions between satisfiable distinct classes, and
/// the unsatisfiable classes. An inconsistent answer carries nothing else.
fn normalise(value: &serde_json::Value) -> Answer {
    let consistent = value["consistent"].as_bool().unwrap();
    if !consistent {
        return (false, BTreeSet::new(), BTreeSet::new());
    }
    let unsat: BTreeSet<String> = names(&value["unsatisfiable"]).into_iter().collect();
    let subs = value["subsumptions"]
        .as_array()
        .unwrap()
        .iter()
        .map(|pair| {
            let pair = names(pair);
            (pair[0].clone(), pair[1].clone())
        })
        .filter(|(sub, sup)| sub != sup && !unsat.contains(sub) && !unsat.contains(sup))
        .collect();
    (true, subs, unsat)
}

fn classify(path: &Path, env: &[(&str, &str)]) -> serde_json::Value {
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars() {
        if key.starts_with("KM_") {
            command.env_remove(key);
        }
    }
    for (key, value) in env {
        command.env(key, value);
    }
    let result = command
        .arg("classify")
        .arg(path)
        .output()
        .expect("run km classification");
    assert!(
        result.status.success(),
        "{}: {}",
        path.display(),
        String::from_utf8_lossy(&result.stderr)
    );
    serde_json::from_slice(&result.stdout).unwrap()
}

fn fixtures() -> Vec<PathBuf> {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/bridge_generator");
    let mut paths: Vec<PathBuf> = std::fs::read_dir(&dir)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "ofn"))
        .collect();
    paths.sort();
    assert!(paths.len() >= 4, "missing fixtures in {}", dir.display());
    paths
}

fn expected(path: &Path) -> Answer {
    let gold = path.with_extension("hermit.json");
    normalise(&serde_json::from_str(&std::fs::read_to_string(gold).unwrap()).unwrap())
}

fn check(paths: &[PathBuf], label: &str, env: &[(&str, &str)]) {
    let mut wrong = Vec::new();
    for path in paths {
        let got = normalise(&classify(path, env));
        let want = expected(path);
        if got != want {
            wrong.push(format!(
                "{} [{label}]: got {got:?}, HermiT {want:?}",
                path.file_name().unwrap().to_string_lossy()
            ));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

#[test]
fn automatic_route_matches_hermit() {
    check(&fixtures(), "auto", &[]);
}

#[test]
fn production_all_route_matches_hermit() {
    check(&fixtures(), "production_all", &[("KM_ROUTE", "production_all")]);
}

/// The minimal cases through both bridge terminologies: the source TBox and
/// the trigger-absorbed clause translation.
#[test]
fn minimal_cases_match_hermit_on_both_bridge_terminologies() {
    let names = [
        "min67_atmost0_definition.ofn",
        "min_atmost1_definition.ofn",
        "min_atleast0_gci.ofn",
        "min_atleast0_nested.ofn",
        "min_copy_successor_insufficient.ofn",
        "clause_or_definer_fallback.ofn",
        "clause_top_conjunction.ofn",
        "clause_top_conjunction_inconsistent.ofn",
        "clause_inverse_exists_negated_filler.ofn",
    ];
    let minimal: Vec<PathBuf> = fixtures()
        .into_iter()
        .filter(|path| names.contains(&path.file_name().unwrap().to_string_lossy().as_ref()))
        .collect();
    assert_eq!(minimal.len(), names.len());
    let bridge = [
        ("KM_ROUTE", "manual"),
        ("KM_MECHANISM", "ht"),
        ("KM_TRIGGER_ABSORB", "1"),
    ];
    check(&minimal, "ht trigger-absorb source-tbox", &bridge);
    let mut clauses = bridge.to_vec();
    clauses.push(("KM_NO_SOURCE_TBOX", "1"));
    check(&minimal, "ht trigger-absorb clauses", &clauses);
}
