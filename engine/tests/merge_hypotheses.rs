//! Wrong answers of the exact nominal routes that are not guard losses
//! (docs/NOMINALS-CB.md section 10). Expected answers are HermiT 1.4.3.456's.
//!
//! * `merge_r1600_min` (minimised from seed r1600 of
//!   `results/agents/2026-10-30/r3-unannounced/gen_r3.py`): `B ⊑ {c}`,
//!   `s(b,c)`, `∃s.B ⊑ {c}`, `c: ∀s.D`; HermiT `B ⊑ D` (a `B` element is `c`,
//!   so `b ∈ ∃s.B`, `b = c`, `s(c,c)` and `D(c)`). The `B` context derives
//!   `⊤ → x ≈ c`; side condition (*) then blocks every r-Succ push from it,
//!   so before the fix the ground context never reasoned under `B(c)`. Fixed
//!   by the merge hypotheses (`Engine::merge_hypotheses`).
//! * `merge_r1600`, `merge_r1646`, `merge_r3602`: the same cause in the
//!   original seeds (`B ⊑ A`, `E ⊑ Q1`, `D ⊑ Q1` missed on `nominals`;
//!   r1600 also on the automatic and `certified_nominals` routes).
//! * `merge_r3403`: `Q3 ≡ {c}`, HermiT `Q3 ⊑ A`. The nominal-label cache read
//!   the types of `c` off the ground context's unit clauses, which the
//!   ordered ground context does not complete (`→ A(c) ∨ c ≈ b` with
//!   `A(b)`). Fixed by using the cache only when every body-free ground
//!   clause is a unit.
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
                let sup = sup.trim_start_matches(':').to_string();
                if sup != "owl:Thing" {
                    subs.insert((sub.trim_start_matches(':').to_string(), sup));
                }
            }
            _ => {}
        }
    }
    subs.retain(|(a, b)| !unsat.contains(a) && !unsat.contains(b) && a != b);
    (consistent, unsat, subs)
}

fn fixture(name: &str) -> String {
    format!("{}/tests/fixtures/nominal_seq_order/{name}", env!("CARGO_MANIFEST_DIR"))
}

fn pairs(list: &[(&str, &str)]) -> BTreeSet<(String, String)> {
    list.iter().map(|(a, b)| (a.to_string(), b.to_string())).collect()
}

fn check(name: &str, route: Option<&str>, subs: &BTreeSet<(String, String)>) {
    let (consistent, unsat, got) = classify(&fixture(name), route, &[]);
    assert!(consistent, "{name} {route:?}");
    assert!(unsat.is_empty(), "{name} {route:?}: {unsat:?}");
    assert_eq!(&got, subs, "{name} {route:?}");
}

fn r1600() -> BTreeSet<(String, String)> {
    pairs(&[("B", "A"), ("D", "A"), ("Q2", "Q1")])
}
fn r1646() -> BTreeSet<(String, String)> {
    pairs(&[("E", "Q1")])
}
fn r3403() -> BTreeSet<(String, String)> {
    pairs(&[("D", "A"), ("D", "Q2"), ("Q1", "A"), ("Q1", "Q3"), ("Q2", "A"), ("Q2", "D"), ("Q3", "A")])
}
fn r3602() -> BTreeSet<(String, String)> {
    pairs(&[("D", "E"), ("D", "Q1"), ("Q1", "D"), ("Q1", "E"), ("Q2", "D"), ("Q2", "E"), ("Q2", "Q1")])
}

#[test]
fn minimised_r1600_on_every_nominal_route() {
    for route in [None, Some("certified_nominals"), Some("nominals")] {
        check("merge_r1600_min.ofn", route, &pairs(&[("B", "D")]));
    }
}

/// Without the merge hypotheses the forced route misses `B ⊑ D`.
#[test]
fn minimised_r1600_needs_the_merge_hypotheses() {
    let (_, _, got) = classify(&fixture("merge_r1600_min.ofn"), Some("nominals"), &[("KM_NO_MERGE_HYPOTHESES", "1")]);
    assert!(!got.contains(&("B".to_string(), "D".to_string())), "{got:?}");
}

#[test]
fn seeds_on_the_automatic_and_certified_routes() {
    for route in [None, Some("certified_nominals")] {
        check("merge_r1600.ofn", route, &r1600());
        check("merge_r1646.ofn", route, &r1646());
        check("merge_r3403.ofn", route, &r3403());
        check("merge_r3602.ofn", route, &r3602());
    }
}

#[test]
fn r3403_on_the_forced_nominals_route() {
    check("merge_r3403.ofn", Some("nominals"), &r3403());
}

/// The exchange cut (docs/PER-CONTEXT-ORDERING.md section 14): seeds whose
/// receivers pushed every ground atom of a delivered clause back as a
/// hypothesis (`r5`: merge hypotheses on four bridges, `r129`: the R3
/// equality deliveries, `r1646`) answer on the forced route, and the cut
/// changes no answer of the minimised r1600.
#[test]
fn exchange_cut_seeds_on_the_forced_nominals_route() {
    check("cut_r5_bridges.ofn", Some("nominals"), &BTreeSet::new());
    check("cut_r129_pushback.ofn", Some("nominals"), &pairs(&[("Q1", "B"), ("Q2", "B")]));
    check("merge_r1646.ofn", Some("nominals"), &r1646());
}

#[test]
fn minimised_r1600_without_the_exchange_cut() {
    for extra in [("KM_NO_EXCHANGE_CUT", "1"), ("KM_NO_MERGE_CUT", "1")] {
        let (consistent, unsat, got) = classify(&fixture("merge_r1600_min.ofn"), Some("nominals"), &[extra]);
        assert!(consistent && unsat.is_empty(), "{extra:?}");
        assert_eq!(got, pairs(&[("B", "D")]), "{extra:?}");
    }
}

/// The forced `nominals` route answers r1600 and r1646 exactly, but slowly:
/// the ground context reasons under the merge hypotheses `B(a)`, `B(c)`
/// (r1600) and `E(a)`, `E(b)` (r1646), and the ground atoms its answers carry
/// back are pushed again as hypotheses (docs/NOMINALS-CB.md section 10).
/// r3602 answered in 6.5 s on this branch at 3ae4185d; merged with a2e98d95
/// it times out at 60 s also with the merge hypotheses and the ranked R2
/// switched off, as does the nominal-coverage binary that development merged.
#[test]
#[ignore = "minutes on the forced nominals route (docs/NOMINALS-CB.md section 10)"]
fn r1600_r3602_on_the_forced_nominals_route() {
    check("merge_r1600.ofn", Some("nominals"), &r1600());
    check("merge_r3602.ofn", Some("nominals"), &r3602());
}
