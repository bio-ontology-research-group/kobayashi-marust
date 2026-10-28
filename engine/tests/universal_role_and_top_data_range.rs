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
    classify_on(text, None)
}

/// As [`classify`], on the named `KM_ROUTE` procedure when one is given.
fn classify_on(text: &str, route: Option<&str>) -> (Answer, Duration) {
    let fixture = Fixture::new(text);
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars_os() {
        if key.to_string_lossy().starts_with("KM_") {
            command.env_remove(key);
        }
    }
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
            panic!("km classify exceeded {BOUND:?} (route {route:?})");
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
/// answer is `F ⊑ T1` only (HermiT agrees). The nominal CB routes used to
/// run forever: every `⊤ ⊑ C` fact, the excluded middle `⊤ ⊑ ¬{1} ⊔ {1}`
/// among them, was instantiated at every ground term, the hub of the
/// universal role included, and the value's at-most-one clause turned
/// every pair into a merge candidate. The frontend's sort encoding
/// (`frontend::sorts`) now keeps `owl:Thing` to the object domain.
#[test]
fn nominal_top_role_reproducer() {
    for route in NOMINAL_ROUTES {
        let (answer, elapsed) = classify_on(NOMINAL_TOP_ROLE, route);
        assert!(elapsed < BOUND, "{route:?}");
        assert!(answer.consistent, "{route:?}");
        assert!(answer.unsat.is_empty(), "{route:?}");
        assert_eq!(answer.subs, pairs(&[("urn:q#F", "urn:q#T1")]), "{route:?}");
    }
}

/// The sort encoding must not make the data value itself unsatisfiable: a
/// marker `D` with `∃link.⊤ ⊑ ¬D` alone would, because the hub axiom is
/// instantiated at the value. `W2 ≡ F ⊓ (u value 1)` and
/// `W3 ≡ S6 ⊓ (u value 1)` stay satisfiable (HermiT: `W2 ⊑ F ⊑ T1`,
/// `W3 ⊑ S6`, nothing unsatisfiable).
#[test]
fn data_value_next_to_universal_role_hub_stays_satisfiable() {
    let text = NOMINAL_TOP_ROLE.replace(
        "\n)",
        "\nDeclaration(Class(<urn:q#W2>)) EquivalentClasses(<urn:q#W2> ObjectIntersectionOf(<urn:q#F> \
         DataHasValue(<http://x/u> \"1\"^^xsd:integer)))\n\
         Declaration(Class(<urn:q#W3>)) EquivalentClasses(<urn:q#W3> ObjectIntersectionOf(<urn:q#S6> \
         DataHasValue(<http://x/u> \"1\"^^xsd:integer)))\n)",
    );
    assert_ne!(text, NOMINAL_TOP_ROLE, "probe classes appended");
    let expected = pairs(&[
        ("urn:q#F", "urn:q#T1"),
        ("urn:q#W2", "urn:q#F"),
        ("urn:q#W2", "urn:q#T1"),
        ("urn:q#W3", "urn:q#S6"),
    ]);
    for route in NOMINAL_ROUTES {
        let (answer, elapsed) = classify_on(&text, route);
        assert!(elapsed < BOUND, "{route:?}");
        assert!(answer.consistent, "{route:?}");
        assert!(answer.unsat.is_empty(), "{route:?}: {:?}", answer.unsat);
        assert_eq!(answer.subs, expected, "{route:?}");
    }
}

/// Data-range-level facts must keep applying to data nodes: with
/// `A ⊑ (u value 2)` and `C ≡ ¬∀u.{1}`, the value `2` is not `1`, so
/// `A ⊑ C` (HermiT agrees). Relativizing the excluded middle
/// `⊤ ⊑ ¬{1} ⊔ {1}` of the complement definer would lose it.
#[test]
fn data_range_complement_excluded_middle_still_applies_to_values() {
    let text = "Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\nOntology(<http://x/o>\n\
        Declaration(DataProperty(<http://x/u>)) Declaration(ObjectProperty(<http://x/r>)) \
        Declaration(NamedIndividual(<urn:q#c>))\n\
        Declaration(Class(<urn:q#A>)) Declaration(Class(<urn:q#C>)) Declaration(Class(<urn:q#S>))\n\
        SubClassOf(<urn:q#A> DataHasValue(<http://x/u> \"2\"^^xsd:integer))\n\
        EquivalentClasses(<urn:q#C> ObjectComplementOf(DataAllValuesFrom(<http://x/u> DataOneOf(\"1\"^^xsd:integer))))\n\
        EquivalentClasses(<urn:q#S> ObjectIntersectionOf(ObjectOneOf(<urn:q#c>) ObjectSomeValuesFrom(<http://x/r> ObjectOneOf(<urn:q#c>))))\n)\n";
    for route in NOMINAL_ROUTES {
        let (answer, elapsed) = classify_on(text, route);
        assert!(elapsed < BOUND, "{route:?}");
        assert!(answer.consistent, "{route:?}");
        assert!(answer.unsat.is_empty(), "{route:?}");
        assert_eq!(answer.subs, pairs(&[("urn:q#A", "urn:q#C")]), "{route:?}");
    }
}

/// The `⊤` definer is shared between `owl:Thing` and the `rdfs:Literal`
/// filler of `≥1 linkURI`, and `DataPropertyRange(uri anyURI)` is written
/// as an implication from it. The sort encoding must relativize that
/// implication like a `⊤ ⊑ C` fact; otherwise the object-sorted range
/// definer is forced on the `linkURI` value and `URLLink` (and `V`) become
/// unsatisfiable, which the `nominals` route reported on ore_ont_14321,
/// 13132 and 6951. HermiT: consistent, nothing unsatisfiable, no
/// subsumption.
#[test]
fn data_property_range_over_the_shared_top_definer_stays_satisfiable() {
    let text = "Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\nOntology(<http://x/o>\n\
        Declaration(Class(<urn:q#URLLink>)) Declaration(Class(<urn:q#Document>)) Declaration(Class(<urn:q#V>))\n\
        Declaration(DataProperty(<urn:q#linkURI>)) Declaration(DataProperty(<urn:q#uri>)) \
        Declaration(DataProperty(<urn:q#u>))\n\
        Declaration(NamedIndividual(<urn:q#a>))\n\
        SubClassOf(<urn:q#URLLink> DataMinCardinality(1 <urn:q#linkURI>))\n\
        SubClassOf(<urn:q#Document> owl:Thing)\n\
        DataPropertyRange(<urn:q#uri> xsd:anyURI)\n\
        ClassAssertion(owl:Thing <urn:q#a>)\n\
        SubClassOf(<urn:q#V> DataHasValue(<urn:q#u> \"1\"^^xsd:integer))\n)\n";
    for route in NOMINAL_ROUTES {
        let (answer, elapsed) = classify_on(text, route);
        assert!(elapsed < BOUND, "{route:?}");
        assert!(answer.consistent, "{route:?}");
        assert!(answer.unsat.is_empty(), "{route:?}: {:?}", answer.unsat);
        assert!(answer.subs.is_empty(), "{route:?}: {:?}", answer.subs);
    }
}

/// The datatype agent's reproducer: `Has ≡ ≥1 d` reifies `⊤` with only
/// data-sorted evidence, `DataPropertyRange(e string)` is written as an
/// implication from that definer, and `V ≡ (e value 1)` clashes with the
/// range. HermiT: consistent, `V` unsatisfiable, nothing else. The
/// `nominals` route used to answer inconsistent.
#[test]
fn data_sorted_top_definer_keeps_data_values_satisfiable() {
    let text = "Prefix(:=<http://example.org/t#>)\nPrefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\n\
        Ontology(<http://example.org/t>\n\
        Declaration(DataProperty(:d)) Declaration(DataProperty(:e)) Declaration(Class(:Has)) \
        Declaration(Class(:V)) Declaration(NamedIndividual(:a))\n\
        EquivalentClasses(:Has DataMinCardinality(1 :d))\n\
        DataPropertyRange(:e xsd:string)\n\
        EquivalentClasses(:V DataHasValue(:e \"1\"^^xsd:integer))\n\
        ClassAssertion(:Has :a)\n)\n";
    for route in NOMINAL_ROUTES {
        let (answer, elapsed) = classify_on(text, route);
        assert!(elapsed < BOUND, "{route:?}");
        assert!(answer.consistent, "{route:?}");
        assert_eq!(answer.unsat, names(&[":V"]), "{route:?}");
        assert!(answer.subs.is_empty(), "{route:?}: {:?}", answer.subs);
    }
}

/// Object and data assertions on the same individual, next to a `⊤ ⊑ ∃r.{b}`
/// fact. Hand derivation: `⊤ ⊑ ∃r.{b} ⊑ B`, so every class is below `B`;
/// `a ∈ A` and `u(a,1)`, so `D ≡ {a} ⊓ (u value 1)` is `{a}` and
/// `E ≡ {a} ⊓ C` is below `D` and `A`; `C ⊒ ¬(u value 1)` does not contain
/// `a` in every model, so `D ⋢ E` (HermiT agrees on the whole table). The
/// data assertions are written as `ClassAssertion(DataHasValue(u v) a)`,
/// the form the frontend always carries (a `DataPropertyAssertion` is
/// converted only when that conversion is enabled). The nominal routes used
/// to run forever on this input as well.
#[test]
fn mixed_object_and_data_assertions_on_one_individual() {
    let text = "Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\nOntology(<http://x/o>\n\
        Declaration(DataProperty(<http://x/u>)) Declaration(ObjectProperty(<http://x/r>))\n\
        Declaration(NamedIndividual(<urn:q#a>)) Declaration(NamedIndividual(<urn:q#b>))\n\
        Declaration(Class(<urn:q#A>)) Declaration(Class(<urn:q#B>)) Declaration(Class(<urn:q#C>)) \
        Declaration(Class(<urn:q#D>)) Declaration(Class(<urn:q#E>))\n\
        ClassAssertion(<urn:q#A> <urn:q#a>)\n\
        ObjectPropertyAssertion(<http://x/r> <urn:q#a> <urn:q#b>)\n\
        ClassAssertion(DataHasValue(<http://x/u> \"1\"^^xsd:integer) <urn:q#a>)\n\
        ClassAssertion(DataHasValue(<http://x/u> \"2\"^^xsd:integer) <urn:q#b>)\n\
        SubClassOf(ObjectSomeValuesFrom(<http://x/r> ObjectOneOf(<urn:q#b>)) <urn:q#B>)\n\
        SubClassOf(ObjectComplementOf(DataHasValue(<http://x/u> \"1\"^^xsd:integer)) <urn:q#C>)\n\
        SubClassOf(owl:Thing ObjectSomeValuesFrom(<http://x/r> ObjectOneOf(<urn:q#b>)))\n\
        EquivalentClasses(<urn:q#D> ObjectIntersectionOf(ObjectOneOf(<urn:q#a>) DataHasValue(<http://x/u> \"1\"^^xsd:integer)))\n\
        EquivalentClasses(<urn:q#E> ObjectIntersectionOf(ObjectOneOf(<urn:q#a>) <urn:q#C>))\n)\n";
    let expected = pairs(&[
        ("urn:q#A", "urn:q#B"),
        ("urn:q#C", "urn:q#B"),
        ("urn:q#D", "urn:q#A"),
        ("urn:q#D", "urn:q#B"),
        ("urn:q#E", "urn:q#A"),
        ("urn:q#E", "urn:q#B"),
        ("urn:q#E", "urn:q#C"),
        ("urn:q#E", "urn:q#D"),
    ]);
    for route in NOMINAL_ROUTES {
        let (answer, elapsed) = classify_on(text, route);
        assert!(elapsed < BOUND, "{route:?}");
        assert!(answer.consistent, "{route:?}");
        assert!(answer.unsat.is_empty(), "{route:?}");
        assert_eq!(answer.subs, expected, "{route:?}");
    }
}

/// Every route that a nominal input can take. `auto` and the three
/// portfolios run the nominal CB calculus as their exact fallback.
const NOMINAL_ROUTES: [Option<&str>; 6] = [
    None,
    Some("nominals"),
    Some("certified_nominals"),
    Some("nominal_ni_abox"),
    Some("certified_card_proxy_abox"),
    Some("default"),
];

fn data_value_case(body: &str) -> String {
    format!(
        "Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\nOntology(<http://x/o>\n\
         Declaration(ObjectProperty(<http://x/r>)) Declaration(ObjectProperty(<http://x/p>))\n\
         Declaration(DataProperty(<http://x/u>))\n\
         Declaration(NamedIndividual(<http://x/a>)) Declaration(NamedIndividual(<urn:q#c>))\n\
         Declaration(NamedIndividual(<urn:q#d>)) Declaration(NamedIndividual(<urn:q#e>))\n\
         Declaration(Class(<urn:q#B>)) Declaration(Class(<urn:q#S3>)) Declaration(Class(<urn:q#S6>))\n\
         Declaration(Class(<urn:q#X>))\n{body}\n)\n"
    )
}

const NOT_VALUE_ONE: &str =
    "SubClassOf(ObjectComplementOf(DataHasValue(<http://x/u> \"1\"^^xsd:integer)) <urn:q#B>)";
const S6_BOTH_WAYS: &str = "EquivalentClasses(<urn:q#S6> ObjectIntersectionOf(ObjectOneOf(<urn:q#c>) \
    ObjectSomeValuesFrom(<http://x/r> ObjectOneOf(<urn:q#d>)) \
    ObjectSomeValuesFrom(ObjectInverseOf(<http://x/r>) ObjectOneOf(<urn:q#d>))))";

/// `¬(u value 1) ⊑ B` with `S6 ≡ {c} ⊓ ∃r.{d} ⊓ ∃r⁻.{d}` (the S3/S6 part of
/// the Protégé bug-1 reproducer). The frontend encodes the value `1` by the
/// at-most-one clause `val(z₁) ∧ val(z₂) → z₁ ≈ z₂`, whose unguarded
/// variables the nominal CB Hyper rule bound to every pair of terms in the
/// ground context; it never finished. The frontend's sort encoding now keeps
/// the value away from object terms (`frontend::sorts`).
///
/// Hand derivation (OWL 2 Direct Semantics): every case is consistent (take
/// `c`, `d` distinct with `r(c,d)`, `r(d,c)`, `a` anywhere, no `u` values, so
/// `B = ⊤`); no named class is unsatisfiable or below another: `S6` and `S3`
/// are singletons that a model may put inside or outside `B` (give `c` the
/// value `1` or not) and that a model may keep apart from each other, and
/// `B` is not below the singletons in a model with three or more elements.
/// `X ⊑ ≥2 u.{1}` is unsatisfiable: two distinct `u`-values that both equal
/// `1` cannot exist.
#[test]
fn data_value_singleton_next_to_nominal_successors() {
    let renamed = data_value_case(
        "Declaration(ObjectProperty(<http://y/link2>)) Declaration(DataProperty(<http://y/score>)) \
         Declaration(NamedIndividual(<urn:z#k>)) Declaration(NamedIndividual(<urn:z#m>)) \
         Declaration(Class(<urn:z#Cls>)) Declaration(Class(<urn:z#Def>)) \
         SubClassOf(ObjectComplementOf(DataHasValue(<http://y/score> \"7\"^^xsd:integer)) <urn:z#Cls>) \
         EquivalentClasses(<urn:z#Def> ObjectIntersectionOf(ObjectOneOf(<urn:z#k>) \
         ObjectSomeValuesFrom(<http://y/link2> ObjectOneOf(<urn:z#m>)) \
         ObjectSomeValuesFrom(ObjectInverseOf(<http://y/link2>) ObjectOneOf(<urn:z#m>))))",
    );
    let reordered = data_value_case(
        "EquivalentClasses(<urn:q#S6> ObjectIntersectionOf(\
         ObjectSomeValuesFrom(ObjectInverseOf(<http://x/r>) ObjectOneOf(<urn:q#d>)) \
         ObjectSomeValuesFrom(<http://x/r> ObjectOneOf(<urn:q#d>)) ObjectOneOf(<urn:q#c>))) \
         SubClassOf(ObjectComplementOf(DataHasValue(<http://x/u> \"1\"^^xsd:integer)) <urn:q#B>)",
    );
    let cases: Vec<(&str, String, &[&str])> = vec![
        ("minimal", data_value_case(&format!("{NOT_VALUE_ONE} {S6_BOTH_WAYS}")), &[]),
        ("renamed", renamed, &[]),
        ("reordered", reordered, &[]),
        (
            "forward successor only",
            data_value_case(&format!(
                "{NOT_VALUE_ONE} EquivalentClasses(<urn:q#S6> ObjectSomeValuesFrom(<http://x/r> ObjectOneOf(<urn:q#d>)))"
            )),
            &[],
        ),
        (
            "object value instead of data value",
            data_value_case(&format!(
                "SubClassOf(ObjectComplementOf(ObjectHasValue(<http://x/p> <urn:q#e>)) <urn:q#B>) {S6_BOTH_WAYS}"
            )),
            &[],
        ),
        (
            "S3 and S6",
            data_value_case(&format!(
                "EquivalentClasses(<urn:q#S3> ObjectIntersectionOf(ObjectOneOf(<http://x/a>) \
                 ObjectComplementOf(DataHasValue(<http://x/u> \"1\"^^xsd:integer)))) {S6_BOTH_WAYS}"
            )),
            &[],
        ),
        (
            "value counting stays exact",
            data_value_case(&format!(
                "{NOT_VALUE_ONE} {S6_BOTH_WAYS} \
                 SubClassOf(<urn:q#X> DataMinCardinality(2 <http://x/u> DataOneOf(\"1\"^^xsd:integer)))"
            )),
            &["urn:q#X"],
        ),
    ];
    for (name, text, unsat) in &cases {
        for route in NOMINAL_ROUTES {
            let (answer, elapsed) = classify_on(text, route);
            assert!(elapsed < BOUND, "{name} on {route:?}");
            assert!(answer.consistent, "{name} on {route:?}");
            assert_eq!(answer.unsat, names(unsat), "{name} on {route:?}");
            assert!(answer.subs.is_empty(), "{name} on {route:?}: {:?}", answer.subs);
        }
    }
}

/// Differential regressions for the object/data sort encoding: the files in
/// `fixtures/sorts_differential` are the datatype agent's reproducers
/// (`max2_three*`: `⊤ ⊑ ≤2 u` and three `u`-values on one individual, which
/// the sort closure used to satisfy by moving the individual into the data
/// sort) and generated seeds that the sort encoding of e054f6b7 answered
/// incompletely (an unconstrained source class was not placed in the object
/// sort, so relativized `⊤` facts did not reach it). Each `.hermit` file is
/// HermiT 1.4's answer (`C` consistency, `U` unsatisfiable, `S` subsumption,
/// full IRIs); the nominal routes must reproduce it exactly.
#[test]
fn sort_encoding_matches_hermit_on_differential_fixtures() {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/sorts_differential");
    let mut checked = 0;
    for entry in std::fs::read_dir(&dir).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().and_then(|e| e.to_str()) != Some("ofn") {
            continue;
        }
        let text = std::fs::read_to_string(&path).unwrap();
        let base = text
            .lines()
            .find_map(|l| l.strip_prefix("Prefix(:=<").and_then(|r| r.strip_suffix(">)")))
            .expect("default prefix")
            .to_string();
        let expand = |name: &str| match name.strip_prefix(':') {
            Some(local) => format!("{base}{local}"),
            None => name.to_string(),
        };
        let reference = std::fs::read_to_string(path.with_extension("hermit")).unwrap();
        let mut consistent = true;
        let mut unsat = BTreeSet::new();
        let mut subs = BTreeSet::new();
        for line in reference.lines() {
            let fields: Vec<&str> = line.split('\t').collect();
            match fields.as_slice() {
                ["C", value] => consistent = *value == "true",
                ["U", class] => {
                    unsat.insert(class.to_string());
                }
                ["S", sub, sup] => {
                    subs.insert((sub.to_string(), sup.to_string()));
                }
                _ => {}
            }
        }
        let name = path.file_name().unwrap().to_string_lossy().to_string();
        for route in [Some("nominals"), Some("certified_nominals")] {
            let (answer, elapsed) = classify_on(&text, route);
            assert!(elapsed < BOUND, "{name} on {route:?}");
            assert_eq!(answer.consistent, consistent, "{name} on {route:?}");
            if !consistent {
                continue;
            }
            let got_unsat: BTreeSet<String> = answer.unsat.iter().map(|c| expand(c)).collect();
            let got_subs: BTreeSet<(String, String)> = answer
                .subs
                .iter()
                .map(|(a, b)| (expand(a), expand(b)))
                .filter(|(a, _)| !got_unsat.contains(a))
                .collect();
            assert_eq!(got_unsat, unsat, "{name} on {route:?}");
            assert_eq!(got_subs, subs, "{name} on {route:?}");
        }
        checked += 1;
    }
    assert!(checked >= 10, "fixtures found: {checked}");
}
