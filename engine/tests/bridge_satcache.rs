//! Regressions for the satisfiable-cached absorption and the satisfiable
//! expander cache replay in the native bridge
//! (results/agents/2026-11-04/bridge-satcache, docs/HYBRID-CB-HT.md
//! section 23).
//!
//! - `nn1064min`: `Q1 ≡ {b} ⊓ ≥2 p.B`, `Q3 ≡ ≤1 r⁻.(∃r.{a})`, `r ≡ p⁻`,
//!   `InverseFunctional(p)`, `b ≠ a`. A `p`-successor of `b` in `∃p⁻.{a}`
//!   would have the two `p`-predecessors `a` and `b`, so `Q1 ⊑ Q3`.
//! - `nn1313min`: `≤1 p⁻.(∃s⁻.({a} ⊓ ¬A)) ⊑ E`, `p ≡ s⁻`,
//!   `InverseFunctional(s)`. An `s`-successor of an `A` element in
//!   `∃p.({a} ⊓ ¬A)` has the `s`-predecessors `a` and the `A` element, which
//!   would be equal, so `A ⊑ E`.
//! - `nn1348min`: `⊤ ⊑ ≤1 r`, `Q5 ≡ ≤0 r`, `Q4 ≡ ≤1 r⁻.(∃r.∃r.{b})`. An
//!   `r`-predecessor of a `Q5` element in `∃r.∃r.{b}` has that element as its
//!   only `r`-successor, which would then need an `r`-successor: `Q5 ⊑ Q4`.
//! - `sat1096min` (from the sibling family): `Q5 ≡ {a} ⊓ ∃p.(∃s⁻.{b})`,
//!   `Q5 ≡ ≤1 s⁻.(∃s.{a})`, `Q4 ≡ {b} ⊓ ∃p⁻.{a}`, two definitions of `Q2`.
//!   An element other than `a` is not in `Q5`, so it has two
//!   `s`-predecessors that are `s`-predecessors of `a`, and then `a ∉ Q5`:
//!   `Q5` is non-empty only in the one-element model, where `Q5 ⊑ Q4`.
//!
//! In each, a successor was answered from a correct satisfiable-expander-cache
//! entry, and the port deferred on the cached node what Konclude does not
//! defer: its functional `≤1 R`, an existential whose successor must be
//! merged into the ancestor, or the merge of an `∃R.{a}` successor into `a`
//! (Konclude's VALUE shortcut links the node to `a`). With
//! `KM_HT_SATEXP_ABSORB_LEGACY=1` every fixture fails again (the negative
//! control below). Each `.hermit.json` holds HermiT 1.4's answer, checked by
//! hand in section 23.
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
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/bridge_satcache");
    let mut paths: Vec<PathBuf> = std::fs::read_dir(&dir)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "ofn"))
        .collect();
    paths.sort();
    assert!(!paths.is_empty(), "missing fixtures in {}", dir.display());
    paths
}

fn expected(path: &Path) -> Answer {
    let gold = path.with_extension("hermit.json");
    normalise(&serde_json::from_str(&std::fs::read_to_string(gold).unwrap()).unwrap())
}

fn check(label: &str, env: &[(&str, &str)]) {
    let mut wrong = Vec::new();
    for path in fixtures() {
        let got = normalise(&classify(&path, env));
        let want = expected(&path);
        if got != want {
            wrong.push(format!(
                "{} [{label}]: got {got:?}, HermiT {want:?}",
                path.file_name().unwrap().to_string_lossy()
            ));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}



const RELEASE: [(&str, &str); 6] = [
    ("KM_HT_DDB", "1"),
    ("KM_HT_NATIVE_FULL", "1"),
    ("KM_CACHE_CONFORMANCE", "1"),
    ("KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE", "1"),
    ("KM_FAST_IRI_GRAMMAR", "1"),
    ("KM_THREADS", "1"),
];

fn with_release(extra: &[(&'static str, &'static str)]) -> Vec<(&'static str, &'static str)> {
    RELEASE.iter().copied().chain(extra.iter().copied()).collect()
}

#[test]
fn automatic_route_matches_hermit() {
    for _ in 0..3 {
        check("auto", &with_release(&[]));
    }
}

#[test]
fn forced_bridge_matches_hermit() {
    for _ in 0..3 {
        check("ht_bridge", &with_release(&[("KM_ROUTE", "ht_bridge")]));
    }
}

#[test]
fn forced_bridge_completion_only_matches_hermit() {
    check(
        "ht_bridge+KM_HT_NO_SATURATION",
        &with_release(&[("KM_ROUTE", "ht_bridge"), ("KM_HT_NO_SATURATION", "1")]),
    );
}

#[test]
fn negative_control_with_the_former_absorption_misses_each() {
    let env = with_release(&[
        ("KM_ROUTE", "ht_bridge"),
        ("KM_HT_SATEXP_ABSORB_LEGACY", "1"),
        // The entailed functional clauses (cb_nn1811) also recover these
        // fixtures, so the control switches them off as well.
        ("KM_HT_NO_ENTAILED_FUNCTIONAL", "1"),
    ]);
    for path in fixtures() {
        let got = normalise(&classify(&path, &env));
        assert_ne!(
            got,
            expected(&path),
            "{}: the fixture no longer needs the absorption fix",
            path.display()
        );
    }
}

/// The 23-axiom reduction of ore_ont_12128 (section 20) under the
/// pre-section-20 schedule (`KM_BRIDGE_SAT_REFUSE_SELF=1`: completion only,
/// satisfiable expander cache installed). Its miss was the cache replay that
/// skipped the AND rule for an entry written before `GO_0003674 ⊑ Function`
/// was applied (section 23). (`KM_BRIDGE_SAT_REFUSE_SELF=1` also turns off
/// the SELF gate of section 20, so the cache is installed here.)
/// `KM_HT_SATEXP_ABSORB_LEGACY=replay` restores the skip and the miss.
#[test]
fn ore12128_reduction_with_the_cache_and_without_the_self_gate() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/bridge_self/ore12128_reduction_expander_cache.ofn");
    let want = expected(&path);
    for route in [&[][..], &[("KM_ROUTE", "ht_bridge")][..]] {
        let mut env = with_release(route);
        env.push(("KM_BRIDGE_SAT_REFUSE_SELF", "1"));
        assert_eq!(normalise(&classify(&path, &env)), want, "{route:?}");
        env.push(("KM_HT_SATEXP_ABSORB_LEGACY", "replay"));
        assert_ne!(
            normalise(&classify(&path, &env)),
            want,
            "{route:?}: the reduction no longer needs the replay fix"
        );
    }
}

/// Why the SELF gate of section 20 stays on the satisfiable expander cache
/// (section 23): on `bridge_reflexive/merge1708_min.ofn` (`⊤ ⊑ ≤1 p⁻`,
/// `InverseFunctional(s)`, `≤1 s⁻ ⊑ B`, `B ⊑ ∃p.Self`, so every element is
/// its own only `p`-predecessor and `⊤ ⊑ Q3 ≡ ≤2 p.C`) a successor hits an
/// entry whose model chose `B` and a `p` self edge, absorbs `B ⊔ ≥2 s⁻`, and
/// never builds the self edge that would merge it into its ancestor. With
/// the gate lifted (`KM_BRIDGE_SELF_SATEXP_NO_GATE=1`) every `X ⊑ Q3` is
/// lost; `bridge_reflexive.rs` pins the answer with the gate.
#[test]
fn self_gate_negative_control_misses_merge1708() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/bridge_reflexive/merge1708_min.ofn");
    let want = expected(&path);
    for route in [&[][..], &[("KM_ROUTE", "ht_bridge")][..]] {
        let mut env = with_release(route);
        assert_eq!(normalise(&classify(&path, &env)), want, "{route:?}");
        env.push(("KM_BRIDGE_SELF_SATEXP_NO_GATE", "1"));
        assert_ne!(
            normalise(&classify(&path, &env)),
            want,
            "{route:?}: merge1708_min no longer needs the SELF gate"
        );
    }
}
