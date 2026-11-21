//! ABox consistency and realization on small knowledge bases (plan part 1b).
//!
//! Regressions: a negative role assertion `¬r(a,c)` was refuted by any
//! `r(a,b)` (the CB worker read the individual `c` like a variable); a `∀`
//! consumer of a transitive role over ground role assertions depended on the
//! order of the assertions; a repeated `SameIndividual` made the native
//! bridge decline and published `DROPPED 1`. Expected rows in
//! `fixtures/abox/*.rows` were produced by HermiT 1.4.3 (consistency and
//! `getTypes`) and are fixed here as oracles.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const CASES: &[&str] = &[
    "negative-assertion-other-target",
    "negative-assertion-same-target",
    "negative-assertion-chain",
    "negative-assertion-inverse",
    "negative-assertion-inverse-clash",
    "negative-transitive-ab-bc",
    "negative-transitive-bc-ab",
    "transitive-forall-ab-bc",
    "transitive-forall-bc-ab",
    "transitive-forall-nominal-ab-bc",
    "transitive-forall-nominal-bc-ab",
    "same-individual-repeated",
];

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/abox").join(name)
}

fn km(path: &Path, options: &[&str]) -> Output {
    km_env(path, options, &[])
}

fn km_env(path: &Path, options: &[&str], env: &[(&str, &str)]) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars() {
        if key.starts_with("KM_") {
            command.env_remove(key);
        }
    }
    command.env("KM_THREADS", "1");
    for (key, value) in env {
        command.env(key, value);
    }
    command.arg("classify").arg("--lines").args(options).arg(path);
    command.output().unwrap()
}

fn rows(text: &str) -> BTreeSet<String> {
    text.lines()
        .filter(|line| line.starts_with("CONSISTENT ") || line.starts_with("TYPE\t"))
        .map(str::to_string)
        .collect()
}

#[test]
fn consistency_and_types_match_hermit() {
    for case in CASES {
        let source = fixture(&format!("{case}.ofn"));
        let expected = rows(&std::fs::read_to_string(fixture(&format!("{case}.rows"))).unwrap());
        for options in [&[][..], &["--realize"][..]] {
            let output = km(&source, options);
            let stdout = String::from_utf8_lossy(&output.stdout);
            assert!(output.status.success(), "{case} {options:?}: {}", String::from_utf8_lossy(&output.stderr));
            assert!(stdout.lines().any(|line| line == "DROPPED 0"), "{case} {options:?}: {stdout}");
            let mut got = rows(&stdout);
            if options.is_empty() {
                got.retain(|row| row.starts_with("CONSISTENT"));
                let consistency: BTreeSet<String> =
                    expected.iter().filter(|row| row.starts_with("CONSISTENT")).cloned().collect();
                assert_eq!(got, consistency, "{case}");
            } else {
                assert_eq!(got, expected, "{case} --realize");
            }
        }
    }
}

/// E19: a functional data property separates `a` from `b`, and a data value
/// is asserted for both individuals; `{a} ⊓ {b}` is unsatisfiable (HermiT).
/// The native bridge answered it satisfiable: a value-singleton merge made a
/// child of `b` the witness of `a`'s `∃g.{0}`, the nominal merge of `b` into
/// `a` pruned that child, and nothing queued `a`'s `∃` again. These inputs
/// reach the bridge again with the saturation coupling on; the second run
/// turns it off (the old E19 stopgap), which must not change the answer.
#[test]
fn shared_data_values_keep_nominal_intersections_unsatisfiable() {
    for (case, env) in ["e19-data-assertions", "e19-data-has-value", "e19-one-shared-value", "e19-swapped-values"]
        .into_iter()
        .flat_map(|case| [(case, None), (case, Some(("KM_BRIDGE_SINGLETON_SATEXP_GATE", "1")))])
    {
        let output = km_env(&fixture(&format!("{case}.ofn")), &[], env.as_slice());
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(output.status.success(), "{case}: {}", String::from_utf8_lossy(&output.stderr));
        let got: BTreeSet<String> = stdout
            .lines()
            .filter(|line| line.starts_with("CONSISTENT ") || line.starts_with("UNSAT\t") || line.starts_with("SUB\t"))
            .map(str::to_string)
            .collect();
        let expected: BTreeSet<String> = std::fs::read_to_string(fixture(&format!("{case}.classes")))
            .unwrap()
            .lines()
            .map(str::to_string)
            .collect();
        assert_eq!(got, expected, "{case} {env:?}");
    }
}

/// A functional data property `d0` has two different values on one
/// individual, so both inputs are inconsistent (HermiT). Object merges made
/// that individual a node the bridge reuses as its own successor; the
/// saturation-caching attempt on it failed, but the stored blocking data
/// marked the whole label as confirmed, so the next retest re-confirmed the
/// node as saturation cached and its merged value successor never met the
/// clash. The automatic route reaches the bridge through the ground-rule
/// data-source path; the forced bridge must agree.
#[test]
fn declined_saturation_cache_keeps_functional_value_clash() {
    for case in ["declined-saturation-cache-merged-values", "declined-saturation-cache-nominal-values"] {
        for env in [&[][..], &[("KM_ROUTE", "ht_bridge")][..]] {
            let output = km_env(&fixture(&format!("{case}.ofn")), &[], env);
            let stdout = String::from_utf8_lossy(&output.stdout);
            assert!(output.status.success(), "{case} {env:?}: {}", String::from_utf8_lossy(&output.stderr));
            assert_eq!(stdout.lines().next(), Some("CONSISTENT 0"), "{case} {env:?}: {stdout}");
        }
    }
}

/// `c` has the `k`-value 2 and `k` is functional, so `c` is in
/// `=1 k.xsd:integer`, hence in `C`, against `{c} ⊑ ¬C`: inconsistent
/// (HermiT). The native bridge made `C` a lazily unfolded definition
/// (`C -> D`, `¬C -> ¬D`) although the absorbed `{c} ⊑ ¬C` fires only on a
/// positive `C`, which a node in `D` never receives.
#[test]
fn nominal_excluded_from_untriggerable_definition_is_inconsistent() {
    let output = km(&fixture("nominal-not-cardinality-equivalence.ofn"), &[]);
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(stdout.lines().next(), Some("CONSISTENT 0"), "{stdout}");
}


/// Two individuals with different values of a restricted data property are
/// different (HermiT: `O + SameIndividual(a b)` is inconsistent). One value
/// is asserted, the other comes from a class (`d0 value 2`) or the
/// restriction comes from the TBox (`A ⊑ ≤1 d1`). The model plan of
/// `--different` merged the two individuals without meeting the clash,
/// because neither of its structures carries the asserted literal as a
/// valued successor, and published no `DIFFERENT` row.
#[test]
fn asserted_data_values_keep_restricted_individuals_different() {
    for (case, row) in [
        ("different-functional-value-from-class", "DIFFERENT\t:a3\t:a5"),
        ("different-at-most-one-data-value", "DIFFERENT\t:a0\t:a3"),
    ] {
        let output = km(&fixture(&format!("{case}.ofn")), &["--realize", "--different"]);
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(output.status.success(), "{case}: {}", String::from_utf8_lossy(&output.stderr));
        assert!(stdout.lines().any(|line| line == "CONSISTENT 1"), "{case}: {stdout}");
        assert!(stdout.lines().any(|line| line == row), "{case}: {stdout}");
    }
}
