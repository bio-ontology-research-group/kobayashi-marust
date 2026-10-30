//! Disjunctive ground equalities across an individual that the query context
//! did not announce (docs/PER-CONTEXT-ORDERING.md section 8). v1.5.4 listed
//! this case as open with no counterexample known; the generator
//! `results/agents/2026-10-30/r3-unannounced/gen_tpl.py` found four motifs
//! that the exact `nominals` route of v1.5.4 misses. Expected answers are
//! HermiT 1.4.3.456's.
//!
//! * `r3_m1_atmost_qualified`: `e: ≤1 r.B`, `r(e,a)`, `r(e,d)`, `B(d)`, `D(d)`,
//!   `a: B ⊔ C`, `C ⊑ E`, `D ⊑ E`, `Q ⊑ {a}`. The ground context holds
//!   `→ E(a) ∨ a ≈ d` with `E(a)` maximal; the `Q` context announced `a` only
//!   and received nothing (unit-only R3). Fixed by the equality closure of the
//!   guard.
//! * `r3_m4_atmost_union`: `b: ≤1 r ⊔ M`, `M ⊑ ∀r.E`, `r(b,c)`, `r(b,d)`,
//!   `D(c)`, `D ⊑ E`, `Q ⊑ {d}`: the same trap with `→ E(d) ∨ d ≈ c` after the
//!   ground context resolves `M(b)`.
//! * `r3_m6_private_equality`: `f: ≤1 r ⊔ M`, `M ⊑ ∀s.E`, `s(f,d)`, `r(f,b)`,
//!   `r(f,c)`, `b ≠ c`, `Q ⊑ {d}`: `→ E(d) ∨ b ≈ c` with the private equality
//!   below the interface atom `E(d)`, which ordered superposition never
//!   refutes. Fixed by R2 for equalities (no ground equality below a ground
//!   atom it shares no individual with).
//! * `r3_m7_two_equalities`: `c: ≤1 r ⊔ ≤1 s`, `r(c,d)`, `r(c,b)`, `s(c,a)`,
//!   `s(c,f)`, `f ≠ a`, `D(d)`, `Q ⊑ {b}`: `→ b ≈ d ∨ a ≈ f` with the private
//!   equality below the interface equality. Fixed by R2 for equalities (no
//!   ground equality below another one).
use std::collections::BTreeSet;
use std::process::Command;

fn classify(path: &str, route: Option<&str>, extra: &[(&str, &str)]) -> (bool, BTreeSet<String>, BTreeSet<(String, String)>) {
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars_os() {
        if key.to_string_lossy().starts_with("KM_") {
            command.env_remove(key);
        }
    }
    if let Some(route) = route {
        command.env("KM_ROUTE", route);
    }
    for (key, value) in extra {
        command.env(key, value);
    }
    let output = command.args(["classify", "--lines", path]).output().unwrap();
    assert!(output.status.success(), "km failed on {path} {route:?}");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let mut consistent = false;
    let mut unsat = BTreeSet::new();
    let mut subs = BTreeSet::new();
    for line in stdout.lines() {
        let fields: Vec<&str> = line.split('\t').collect();
        match fields.as_slice() {
            [single] if single.starts_with("CONSISTENT ") => consistent = single.ends_with(" 1"),
            ["UNSAT", class] => {
                unsat.insert(class.trim_start_matches(':').to_string());
            }
            ["SUB", sub, sup] => {
                subs.insert((sub.trim_start_matches(':').to_string(), sup.trim_start_matches(':').to_string()));
            }
            _ => {}
        }
    }
    subs.retain(|(a, b)| !unsat.contains(a) && !unsat.contains(b));
    (consistent, unsat, subs)
}

fn fixture(name: &str) -> String {
    format!("{}/tests/fixtures/nominal_seq_order/{name}", env!("CARGO_MANIFEST_DIR"))
}

fn pairs(list: &[(&str, &str)]) -> BTreeSet<(String, String)> {
    list.iter().map(|(a, b)| (a.to_string(), b.to_string())).collect()
}

fn expected() -> Vec<(&'static str, BTreeSet<(String, String)>)> {
    vec![
        ("r3_m1_atmost_qualified.ofn", pairs(&[("C", "E"), ("D", "E"), ("Q", "E")])),
        ("r3_m4_atmost_union.ofn", pairs(&[("D", "E"), ("Q", "E")])),
        ("r3_m6_private_equality.ofn", pairs(&[("D", "E"), ("Q", "E")])),
        ("r3_m7_two_equalities.ofn", pairs(&[("D", "E"), ("Q", "D"), ("Q", "E")])),
    ]
}

const ROUTES: [Option<&str>; 3] = [None, Some("certified_nominals"), Some("nominals")];

#[test]
fn disjunctive_ground_equalities_match_hermit_on_every_nominal_route() {
    for (name, subs) in expected() {
        for route in ROUTES {
            let (consistent, unsat, got) = classify(&fixture(name), route, &[]);
            assert!(consistent, "{name} {route:?}");
            assert!(unsat.is_empty(), "{name} {route:?}: {unsat:?}");
            assert_eq!(got, subs, "{name} {route:?}");
        }
    }
}

/// The base context regime (`KM_NO_SEQ_ORDER` in nominal mode) carries the
/// same R2 and R3. `m7` is left out: forced into the base regime (which the
/// router never selects for it, since its clausification has an internal
/// disjunction) the ground context's unordered same-term Hyper joins run for
/// minutes (docs/PER-CONTEXT-ORDERING.md section 8.5).
#[test]
fn disjunctive_ground_equalities_under_the_base_context_regime() {
    for (name, subs) in expected().into_iter().filter(|(name, _)| !name.starts_with("r3_m7")) {
        let (consistent, unsat, got) = classify(&fixture(name), Some("nominals"), &[("KM_NO_SEQ_ORDER", "1")]);
        assert!(consistent, "{name}");
        assert!(unsat.is_empty(), "{name}: {unsat:?}");
        assert_eq!(got, subs, "{name}");
    }
}

/// The v1.5.4 rules, restored by the diagnostics, miss the query subsumption:
/// unit-only R3 on `m1` and `m4`, R2 without its equality comparisons on `m6`
/// and `m7`. This pins down which part of the fix each fixture needs. Since
/// the ranked guard (docs/PER-CONTEXT-ORDERING.md section 10) delivers the
/// private equalities of `m6` and `m7`, the old comparisons alone answer
/// them; `KM_CONTEXT_PAIR_R2` restores the guard of section 8 as well.
#[test]
fn v154_rules_miss_the_motifs() {
    for (name, flags) in [
        ("r3_m1_atmost_qualified.ofn", &[("KM_CONTEXT_UNIT_R3", "1")][..]),
        ("r3_m4_atmost_union.ofn", &[("KM_CONTEXT_UNIT_R3", "1")][..]),
        ("r3_m6_private_equality.ofn", &[("KM_CONTEXT_NO_EQ_R2", "1"), ("KM_CONTEXT_PAIR_R2", "1")][..]),
        ("r3_m7_two_equalities.ofn", &[("KM_CONTEXT_NO_EQ_R2", "1"), ("KM_CONTEXT_PAIR_R2", "1")][..]),
    ] {
        let (_, _, got) = classify(&fixture(name), Some("nominals"), flags);
        assert!(!got.contains(&("Q".to_string(), "E".to_string())), "{name} {flags:?}: {got:?}");
    }
}

/// The section-8 rules (`KM_CONTEXT_PAIR_R2`) still answer every motif.
#[test]
fn pair_r2_answers_the_motifs() {
    for (name, subs) in expected() {
        let (consistent, unsat, got) = classify(&fixture(name), Some("nominals"), &[("KM_CONTEXT_PAIR_R2", "1")]);
        assert!(consistent, "{name}");
        assert!(unsat.is_empty(), "{name}: {unsat:?}");
        assert_eq!(got, subs, "{name}");
    }
}
