//! Regressions found by the v1.7.0 TBox route sweep (random SROIQ TBoxes,
//! every route forced with `KM_ROUTE`, compared with HermiT 1.4.3.456).
//!
//! * Operands of n-ary disjointness axioms form a set. `DisjointClasses(B D D)`
//!   was read pairwise by position, giving `D ⊓ D ⊑ ⊥`, so `D` was
//!   unsatisfiable on every route.
//! * A named class that occurs only as a qualified cardinality filler got its
//!   HT concept id after the HT query list was built, so the HT card arms (and
//!   the default route, which races them) left it out of the taxonomy.
//! * The legacy tableau's caching checker refuted satisfiable seeds when a
//!   clause had a negative head literal (the complementary-definer fold), and
//!   published wrong subsumptions with `DROPPED 0`.
//!
//! Each case states the expected answer, derived by hand and confirmed with
//! HermiT, and checks it on the default route and on the routes that showed
//! the error.
use std::collections::BTreeSet;
use std::io::Read;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

const BOUND: Duration = Duration::from_secs(60);
static NEXT: AtomicUsize = AtomicUsize::new(0);

struct Fixture(PathBuf);
impl Fixture {
    fn new(text: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "km-tbox-sweep-{}-{}.ofn",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::write(&path, text).unwrap();
        Self(path)
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

#[derive(Debug, PartialEq, Eq)]
struct Answer {
    dropped: String,
    unsat: BTreeSet<String>,
    subs: BTreeSet<(String, String)>,
}

/// `km classify --lines` on `route` (`None` = the default policy), with every
/// ambient `KM_*` variable removed and the child killed after `BOUND`.
fn classify(text: &str, route: Option<&str>) -> Answer {
    let fixture = Fixture::new(text);
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars_os() {
        if key.to_string_lossy().starts_with("KM_") {
            command.env_remove(key);
        }
    }
    command.env("KM_THREADS", "1");
    if let Some(route) = route {
        command.env("KM_ROUTE", route);
    }
    command
        .args(["classify", "--lines"])
        .arg(&fixture.0)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let started = Instant::now();
    let mut child = command.spawn().unwrap();
    loop {
        if let Some(status) = child.try_wait().unwrap() {
            let mut stdout = String::new();
            child.stdout.take().unwrap().read_to_string(&mut stdout).unwrap();
            let mut stderr = String::new();
            child.stderr.take().unwrap().read_to_string(&mut stderr).unwrap();
            assert!(status.success(), "km failed on route {route:?}: {stderr}\n{stdout}");
            return parse(&stdout);
        }
        if started.elapsed() > BOUND {
            let _ = child.kill();
            let _ = child.wait();
            panic!("km classify exceeded {BOUND:?} on route {route:?}:\n{text}");
        }
        std::thread::sleep(Duration::from_millis(20));
    }
}

fn parse(stdout: &str) -> Answer {
    let mut dropped = String::new();
    let mut unsat = BTreeSet::new();
    let mut subs = BTreeSet::new();
    for line in stdout.lines() {
        let fields: Vec<&str> = line.split('\t').collect();
        match fields.as_slice() {
            ["UNSAT", class] => {
                unsat.insert(class.trim_start_matches(':').to_string());
            }
            ["SUB", sub, sup] => {
                subs.insert((
                    sub.trim_start_matches(':').to_string(),
                    sup.trim_start_matches(':').to_string(),
                ));
            }
            _ if line.starts_with("DROPPED ") => dropped = line.to_string(),
            _ => {}
        }
    }
    Answer { dropped, unsat, subs }
}

fn ontology(classes: &[&str], roles: &[&str], axioms: &str) -> String {
    let mut text = String::from(
        "Prefix(:=<http://ex.org/>)\nPrefix(owl:=<http://www.w3.org/2002/07/owl#>)\nOntology(<http://ex.org/t>\n",
    );
    for class in classes {
        text.push_str(&format!("Declaration(Class(:{class}))\n"));
    }
    for role in roles {
        text.push_str(&format!("Declaration(ObjectProperty(:{role}))\n"));
    }
    text.push_str(axioms);
    text.push_str("\n)\n");
    text
}

fn expected(unsat: &[&str], subs: &[(&str, &str)]) -> Answer {
    Answer {
        dropped: "DROPPED 0".to_string(),
        unsat: unsat.iter().map(|c| c.to_string()).collect(),
        subs: subs.iter().map(|(a, b)| (a.to_string(), b.to_string())).collect(),
    }
}

/// Sweep case bool20030_0045, reduced: a repeated operand does not make a
/// class disjoint from itself, in any of the n-ary disjointness axioms.
#[test]
fn repeated_disjointness_operands_form_a_set() {
    let text = ontology(
        &["A", "B", "C", "D", "E"],
        &["r", "s"],
        "DisjointClasses(:B :D :D)\n\
         DisjointUnion(:E :A :C :C)\n\
         DisjointObjectProperties(:r :s :s)\n\
         SubClassOf(:A ObjectSomeValuesFrom(:s owl:Thing))",
    );
    // E ≡ A ⊔ C with A, C disjoint; nothing is unsatisfiable.
    let answer = expected(&[], &[("A", "E"), ("C", "E")]);
    for route in [None, Some("cb_plain1"), Some("ht_bridge"), Some("certified_nominals")] {
        assert_eq!(classify(&text, route), answer, "route {route:?}");
    }
}

/// A one-element operand set after removing repeats follows OWL API 4.5.29
/// (and so Protégé and HermiT): `DisjointClasses(A A)` gets `owl:Thing` added
/// and makes `A` unsatisfiable; the other n-ary axioms have no effect.
#[test]
fn singleton_operand_sets_follow_the_owl_api() {
    let cases: &[(&str, &[&str], &[(&str, &str)])] = &[
        ("DisjointClasses(:A :A)", &["A"], &[]),
        ("DisjointClasses(:A :A :A)", &["A"], &[]),
        ("DisjointUnion(:C :A :A)", &[], &[("A", "C"), ("C", "A")]),
        ("DisjointObjectProperties(:r :r)\nSubClassOf(:A ObjectSomeValuesFrom(:r :C))", &[], &[]),
        ("DisjointDataProperties(:d :d)\nSubClassOf(:A DataSomeValuesFrom(:d xsd:integer))", &[], &[]),
        ("EquivalentClasses(:C :C)", &[], &[]),
        ("EquivalentObjectProperties(:r :r)", &[], &[]),
        ("SameIndividual(:a :a)\nClassAssertion(:A :a)", &[], &[]),
        ("DifferentIndividuals(:a :a)\nClassAssertion(:A :a)", &[], &[]),
    ];
    for (axioms, unsat, subs) in cases {
        let text = ontology(
            &["A", "C"],
            &["r"],
            &format!(
                "Declaration(DataProperty(:d))\nDeclaration(NamedIndividual(:a))\n{axioms}"
            ),
        )
        .replace(
            "Prefix(owl:",
            "Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\nPrefix(owl:",
        );
        assert_eq!(classify(&text, None), expected(unsat, subs), "{axioms}");
    }
}

/// `DifferentIndividuals(a a b)` does not make `a` different from itself, so
/// the ontology stays consistent.
#[test]
fn repeated_different_individuals_operand_is_consistent() {
    let text = ontology(
        &["A"],
        &[],
        "Declaration(NamedIndividual(:a))\nDeclaration(NamedIndividual(:b))\n\
         DifferentIndividuals(:a :a :b)\nClassAssertion(:A :a)",
    );
    let answer = expected(&[], &[]);
    for route in [None, Some("certified_nominals")] {
        assert_eq!(classify(&text, route), answer, "route {route:?}");
    }
}

/// Sweep case card20044_0044, reduced: `D` occurs only as the filler of a
/// qualified cardinality. `B ≡ F ⊓ A` is unsatisfiable (A needs three
/// distinct `s0` successors, `s0` is functional), so `E ≡ ¬B` is `⊤` and
/// every satisfiable class, `D` included, is below `E`.
#[test]
fn cardinality_only_filler_stays_in_the_taxonomy() {
    let text = ontology(
        &["A", "B", "D", "E", "F"],
        &["s0", "s2"],
        "EquivalentClasses(:B ObjectIntersectionOf(:F :A))\n\
         FunctionalObjectProperty(:s0)\n\
         SubClassOf(:A ObjectSomeValuesFrom(:s2 ObjectMinCardinality(3 :s0 :D)))\n\
         EquivalentClasses(:E ObjectComplementOf(:B))",
    );
    let answer = expected(&["A", "B"], &[("D", "E"), ("F", "E")]);
    for route in [None, Some("production_all"), Some("ht_card"), Some("ht_full"), Some("cb_plain1")] {
        assert_eq!(classify(&text, route), answer, "route {route:?}");
    }
}

/// Sweep case bool20033_0082, reduced: `C` occurs in no axiom, so its only
/// named subsumer is itself. The tableau route published `C ⊑ Q1`
/// (`Q1 ≡ ¬B`).
#[test]
fn tableau_cache_does_not_refute_satisfiable_seeds_after_the_complement_fold() {
    let text = ontology(
        &["A", "B", "C", "Q0", "Q1"],
        &["s0"],
        "EquivalentClasses(:Q1 ObjectComplementOf(:B))\n\
         SubClassOf(:B ObjectSomeValuesFrom(:s0 :A))\n\
         SubClassOf(ObjectIntersectionOf(:B ObjectComplementOf(:A)) :Q0)",
    );
    let answer = expected(&[], &[]);
    for route in [None, Some("tableau"), Some("cb_plain1")] {
        assert_eq!(classify(&text, route), answer, "route {route:?}");
    }
}
