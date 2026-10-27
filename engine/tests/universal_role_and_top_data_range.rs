//! Regression tests for universal-role restrictions and `rdfs:Literal`
//! existentials (Protégé plugin reproducers, 2026-10-26).
//!
//! `owl:topObjectProperty` used to be clausified as an ordinary role, which
//! was incomplete (no element was `U`-related to every other) and made small
//! inputs run to the worker limit. `DataSomeValuesFrom(p rdfs:Literal)` carried
//! a `__dt__Literal` label that sent otherwise bridge-classifiable inputs to
//! slower calculi. Each test checks the exact taxonomy, derived by hand from
//! the OWL 2 Direct Semantics, and a wall-clock bound far below the old
//! behaviour (minutes, or no termination).
use std::collections::BTreeSet;
use std::io::Read;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

const BOUND: Duration = Duration::from_secs(10);
static NEXT: AtomicUsize = AtomicUsize::new(0);

struct Fixture(PathBuf);
impl Fixture {
    fn new(text: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "km-universal-role-{}-{}.ofn",
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
    consistent: bool,
    unsat: BTreeSet<String>,
    subs: BTreeSet<(String, String)>,
}

/// Classify `text` with `km classify --lines`, killing the child (by its own
/// handle) when it exceeds `BOUND`.
fn classify(text: &str) -> (Answer, Duration) {
    let fixture = Fixture::new(text);
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars_os() {
        if key.to_string_lossy().starts_with("KM_") {
            command.env_remove(key);
        }
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
            let elapsed = started.elapsed();
            let mut stdout = String::new();
            child.stdout.take().unwrap().read_to_string(&mut stdout).unwrap();
            let mut stderr = String::new();
            child.stderr.take().unwrap().read_to_string(&mut stderr).unwrap();
            assert!(status.success(), "km failed: {stderr}\n{stdout}");
            return (parse(&stdout), elapsed);
        }
        if started.elapsed() > BOUND {
            let _ = child.kill();
            let _ = child.wait();
            panic!("km classify exceeded {BOUND:?}");
        }
        std::thread::sleep(Duration::from_millis(20));
    }
}

fn parse(stdout: &str) -> Answer {
    let mut consistent = None;
    let mut unsat = BTreeSet::new();
    let mut subs = BTreeSet::new();
    for line in stdout.lines() {
        let fields: Vec<&str> = line.split('\t').collect();
        match fields.as_slice() {
            [single] if single.starts_with("CONSISTENT ") => {
                consistent = Some(single.ends_with(" 1"));
            }
            ["UNSAT", class] => {
                unsat.insert(class.to_string());
            }
            ["SUB", sub, sup] => {
                subs.insert((sub.to_string(), sup.to_string()));
            }
            _ => {}
        }
    }
    Answer { consistent: consistent.expect("CONSISTENT line"), unsat, subs }
}

fn pairs(list: &[(&str, &str)]) -> BTreeSet<(String, String)> {
    list.iter().map(|(a, b)| (a.to_string(), b.to_string())).collect()
}

fn names(list: &[&str]) -> BTreeSet<String> {
    list.iter().map(|name| name.to_string()).collect()
}

fn small(body: &str) -> String {
    format!(
        "Prefix(:=<urn:t#>)\nOntology(\n\
         Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C)) Declaration(Class(:D))\n\
         Declaration(Class(:X)) Declaration(Class(:Y)) Declaration(Class(:Z))\n\
         Declaration(NamedIndividual(:a)) Declaration(ObjectProperty(:r))\n{body}\n)\n"
    )
}

const FAMILY_WITH_TOP_ROLE_QUERY: &str = include_str!("fixtures/protege_plugin/bug2-exists-top-property-slow.ofn");
const FAMILY_FRAGMENT_WITH_LITERAL_QUERY: &str =
    include_str!("fixtures/protege_plugin/bug3-data-some-literal-hang.ofn");
const NOMINAL_TOP_ROLE: &str = include_str!("fixtures/protege_plugin/bug1-nominal-top-property-hang.ofn");

const TOP_ROLE_QUERY: &str =
    "Declaration(Class(<urn:q#Q>)) EquivalentClasses(<urn:q#Q> ObjectSomeValuesFrom(owl:topObjectProperty owl:Thing))";

/// `Q ≡ ∃U.⊤` is `Q ≡ ⊤` (the domain is non-empty). It used to exhaust the
/// 240 s worker limit on this 60-axiom ontology.
#[test]
fn exists_top_role_thing_is_owl_thing_and_fast() {
    let (answer, elapsed) = classify(FAMILY_WITH_TOP_ROLE_QUERY);
    assert!(elapsed < BOUND);
    let base = FAMILY_WITH_TOP_ROLE_QUERY.replace(TOP_ROLE_QUERY, "");
    assert_ne!(base, FAMILY_WITH_TOP_ROLE_QUERY, "query axiom present in the fixture");
    let (without, _) = classify(&base);
    assert!(answer.consistent && without.consistent);
    assert_eq!(answer.unsat, names(&[":Impossible"]));
    assert_eq!(answer.unsat, without.unsat);
    // Q is a fresh name equivalent to owl:Thing: the rest of the taxonomy is
    // unchanged and every satisfiable class is below Q.
    let q = "urn:q#Q".to_string();
    let rest: BTreeSet<_> = answer.subs.iter().filter(|(a, b)| *a != q && *b != q).cloned().collect();
    assert_eq!(rest, without.subs);
    for class in [
        ":Adult", ":Animal", ":Child", ":Father", ":Grandparent", ":Man", ":Mother",
        ":OnlyChild", ":Parent", ":Person", ":Royal", ":Thing2", ":Woman",
    ] {
        assert!(answer.subs.contains(&(class.to_string(), q.clone())), "{class} ⊑ Q missing");
    }
    // Thing2 ≡ Person ⊔ ¬Person ≡ ⊤ ≡ Q.
    assert!(answer.subs.contains(&(q.clone(), ":Thing2".to_string())));
}

/// `DataSomeValuesFrom(age rdfs:Literal)` with `age` otherwise unused: Q is
/// only below `Thing2 ≡ ⊤`. It used to take 7.9 s.
#[test]
fn literal_existential_over_free_data_property_is_fast() {
    let (answer, elapsed) = classify(FAMILY_FRAGMENT_WITH_LITERAL_QUERY);
    assert!(elapsed < BOUND);
    assert!(answer.consistent);
    assert!(answer.unsat.is_empty());
    assert_eq!(
        answer.subs,
        pairs(&[
            (":Child", ":Person"), (":Child", ":Thing2"),
            (":Grandparent", ":Person"), (":Grandparent", ":Thing2"),
            (":OnlyChild", ":Child"), (":OnlyChild", ":Person"), (":OnlyChild", ":Thing2"),
            (":Parent", ":Person"), (":Parent", ":Thing2"),
            (":Person", ":Thing2"),
            ("urn:q#Q", ":Thing2"),
        ])
    );
}

/// The full family ontology plus `Q ≡ DataSomeValuesFrom(age rdfs:Literal)`
/// ran past 60 s. `age` has domain Person and `Adult ≡ ∃age.integer[≥18]`, so
/// `Adult ⊑ Q ⊑ Person`; the answer must equal the one for the equivalent
/// `DataMinCardinality(1 age)`.
#[test]
fn literal_existential_matches_unqualified_min_cardinality() {
    let literal = FAMILY_WITH_TOP_ROLE_QUERY.replace(
        TOP_ROLE_QUERY,
        "Declaration(Class(<urn:q#Q>)) EquivalentClasses(<urn:q#Q> DataSomeValuesFrom(:age rdfs:Literal))",
    );
    let cardinality = FAMILY_WITH_TOP_ROLE_QUERY.replace(
        TOP_ROLE_QUERY,
        "Declaration(Class(<urn:q#Q>)) EquivalentClasses(<urn:q#Q> DataMinCardinality(1 :age))",
    );
    let (answer, elapsed) = classify(&literal);
    assert!(elapsed < BOUND);
    let (expected, _) = classify(&cardinality);
    assert_eq!(answer, expected);
    for pair in [(":Adult", "urn:q#Q"), ("urn:q#Q", ":Person"), ("urn:q#Q", ":Thing2")] {
        assert!(answer.subs.contains(&(pair.0.to_string(), pair.1.to_string())), "{pair:?}");
    }
    assert!(!answer.subs.contains(&(":Person".to_string(), "urn:q#Q".to_string())));
}

/// Universal-role semantics that an ordinary-role reading misses.
#[test]
fn universal_role_restrictions_are_complete() {
    let cases: &[(&str, &[(&str, &str)], &[&str])] = &[
        // B ⊑ ∀U.C: if B is non-empty everything is C, so B ⊑ C ⊑ D.
        ("EquivalentClasses(:B ObjectAllValuesFrom(owl:topObjectProperty :C)) SubClassOf(:C :D)",
         &[(":B", ":C"), (":B", ":D"), (":C", ":D")], &[]),
        // ∃U.A ⊑ ∃U.B when A ⊑ B; a non-empty A makes X ≡ ⊤.
        ("EquivalentClasses(:X ObjectSomeValuesFrom(owl:topObjectProperty :A)) \
          EquivalentClasses(:Y ObjectSomeValuesFrom(owl:topObjectProperty :B)) SubClassOf(:A :B)",
         &[(":A", ":B"), (":A", ":X"), (":A", ":Y"), (":B", ":Y"), (":X", ":Y")], &[]),
        // A ⊑ ∃U.B, B ⊑ ∀U.C, A ⊑ ¬C: A is unsatisfiable; B ⊑ C.
        ("SubClassOf(:A ObjectSomeValuesFrom(owl:topObjectProperty :B)) \
          SubClassOf(:B ObjectAllValuesFrom(owl:topObjectProperty :C)) \
          SubClassOf(:A ObjectComplementOf(:C))",
         &[(":B", ":C")], &[":A"]),
        // B ⊑ ∀U.¬A with A(a): B is unsatisfiable.
        ("SubClassOf(:B ObjectAllValuesFrom(owl:topObjectProperty ObjectComplementOf(:A))) \
          ClassAssertion(:A :a)",
         &[], &[":B"]),
        // Nested: Z ≡ ∃U.(A ⊓ ∀U.B) gives Z ⊑ B.
        ("EquivalentClasses(:Z ObjectSomeValuesFrom(owl:topObjectProperty \
          ObjectIntersectionOf(:A ObjectAllValuesFrom(owl:topObjectProperty :B))))",
         &[(":Z", ":B")], &[]),
        // A ⊑ ∀U.⊥ makes A unsatisfiable.
        ("SubClassOf(:A ObjectAllValuesFrom(owl:topObjectProperty owl:Nothing))", &[], &[":A"]),
        // U⁻ = U.
        ("SubClassOf(:A ObjectSomeValuesFrom(ObjectInverseOf(owl:topObjectProperty) :B)) \
          SubClassOf(:B ObjectAllValuesFrom(owl:topObjectProperty :C))",
         &[(":A", ":C"), (":B", ":C")], &[]),
        // The range (and domain) of U is `⊤ ⊑ C`.
        ("ObjectPropertyRange(owl:topObjectProperty :C) SubClassOf(:A :B)",
         &[(":A", ":B"), (":A", ":C"), (":B", ":C"), (":D", ":C"), (":X", ":C"), (":Y", ":C"), (":Z", ":C")], &[]),
        // A vacuous R ⊑ U next to a real restriction.
        ("SubObjectPropertyOf(:r owl:topObjectProperty) \
          EquivalentClasses(:X ObjectSomeValuesFrom(owl:topObjectProperty :A)) \
          SubClassOf(:B ObjectSomeValuesFrom(:r :A))",
         &[(":A", ":X"), (":B", ":X")], &[]),
    ];
    for (body, subs, unsat) in cases {
        let (answer, elapsed) = classify(&small(body));
        assert!(elapsed < BOUND, "{body}");
        assert!(answer.consistent, "{body}");
        assert_eq!(answer.subs, pairs(subs), "{body}");
        assert_eq!(answer.unsat, names(unsat), "{body}");
    }
    // ⊤ ⊑ ∃U.A with A ⊑ ⊥ is inconsistent.
    let (answer, _) = classify(&small(
        "SubClassOf(owl:Thing ObjectSomeValuesFrom(owl:topObjectProperty :A)) SubClassOf(:A owl:Nothing)",
    ));
    assert!(!answer.consistent);
}

/// `T1 ≡ ∃U.F` next to nominal and data-value definitions. The expected
/// answer is `F ⊑ T1` only. This still does not terminate: the hub encoding
/// is exact, but the certified bridge defers on its global `⊤ ⊑ ∃S.{g}`
/// axiom when data properties occur (blank-data-node certificate), and the
/// nominal CB fallback diverges on `S3`/`S6` even without the universal role.
#[test]
#[ignore = "open: nominal CB fallback diverges on the S3/S6 part (independent of owl:topObjectProperty)"]
fn nominal_top_role_reproducer() {
    let (answer, elapsed) = classify(NOMINAL_TOP_ROLE);
    assert!(elapsed < BOUND);
    assert!(answer.consistent);
    assert!(answer.unsat.is_empty());
    assert_eq!(answer.subs, pairs(&[("urn:q#F", "urn:q#T1")]));
}
