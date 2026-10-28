//! Positive data-property assertions on the clause routes.
//!
//! `DataPropertyAssertion(p a v)` holds iff `a` is an instance of
//! `DataHasValue(p v)` (OWL 2 Direct Semantics). The frontend carried the
//! assertion as that class assertion only inside the native bridge attempt;
//! every clause route (the nominal CB routes, and the automatic route once the
//! bridge declined) dropped it and published a complete-looking taxonomy with
//! `DROPPED 0`, missing `E ⊑ D` in `DataHasValue(u 1) ⊑ D, E ≡ {a},
//! DataPropertyAssertion(u a 1)`. The orchestrator now re-runs the frontend
//! with the conversion whenever it reports uncarried assertions whose drop is
//! not certified harmless, on every route, and publishes whatever stays
//! uncarried (negative assertions, a literal vocabulary above the cap) as
//! dropped axioms. Expected taxonomies are hand derived and agree with HermiT
//! 1.4.3.456.
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
            "km-data-assertions-{}-{}.ofn",
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
    dropped: usize,
    unsat: BTreeSet<String>,
    subs: BTreeSet<(String, String)>,
}

fn classify(text: &str, route: Option<&str>) -> Answer {
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
    let mut consistent = None;
    let mut dropped = None;
    let mut unsat = BTreeSet::new();
    let mut subs = BTreeSet::new();
    for line in stdout.lines() {
        let fields: Vec<&str> = line.split('\t').collect();
        match fields.as_slice() {
            [single] if single.starts_with("CONSISTENT ") => consistent = Some(single.ends_with(" 1")),
            [single] if single.starts_with("DROPPED ") => {
                dropped = single["DROPPED ".len()..].trim().parse().ok();
            }
            ["UNSAT", class] => {
                unsat.insert(class.trim_start_matches(':').to_string());
            }
            ["SUB", sub, sup] => {
                subs.insert((sub.trim_start_matches(':').to_string(), sup.trim_start_matches(':').to_string()));
            }
            _ => {}
        }
    }
    Answer {
        consistent: consistent.expect("CONSISTENT line"),
        dropped: dropped.expect("DROPPED line"),
        unsat,
        subs,
    }
}

fn pairs(list: &[(&str, &str)]) -> BTreeSet<(String, String)> {
    list.iter().map(|(a, b)| (a.to_string(), b.to_string())).collect()
}

const HEADER: &str = "Prefix(:=<http://example.org/t#>)\n\
    Prefix(owl:=<http://www.w3.org/2002/07/owl#>)\n\
    Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\n\
    Ontology(<http://example.org/t>\n\
    Declaration(DataProperty(:u)) Declaration(Class(:D)) Declaration(Class(:E)) \
    Declaration(NamedIndividual(:a))\n";

/// The routes that carry an ABox: the default policy and the nominal arms.
const ROUTES: [Option<&str>; 4] = [None, Some("nominals"), Some("certified_nominals"), Some("default")];

const SINGLE: &str = "SubClassOf(DataHasValue(:u \"1\"^^xsd:integer) :D)\n\
    EquivalentClasses(:E ObjectOneOf(:a))\n\
    DataPropertyAssertion(:u :a \"1\"^^xsd:integer)\n";

#[test]
fn single_data_assertion_is_carried_on_every_abox_route() {
    let text = format!("{HEADER}{SINGLE})\n");
    for route in ROUTES {
        let answer = classify(&text, route);
        assert_eq!(
            answer,
            Answer { consistent: true, dropped: 0, unsat: BTreeSet::new(), subs: pairs(&[("E", "D")]) },
            "route {route:?}"
        );
    }
}

/// The mixed object-and-data input of
/// `universal_role_and_top_data_range::mixed_object_and_data_assertions_on_one_individual`,
/// written with literal `DataPropertyAssertion` axioms.
#[test]
fn mixed_object_and_data_assertions_are_carried() {
    let text = "Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\nOntology(<http://x/o>\n\
        Declaration(DataProperty(<http://x/u>)) Declaration(ObjectProperty(<http://x/r>))\n\
        Declaration(NamedIndividual(<urn:q#a>)) Declaration(NamedIndividual(<urn:q#b>))\n\
        Declaration(Class(<urn:q#A>)) Declaration(Class(<urn:q#B>)) Declaration(Class(<urn:q#C>)) \
        Declaration(Class(<urn:q#D>)) Declaration(Class(<urn:q#E>))\n\
        ClassAssertion(<urn:q#A> <urn:q#a>)\n\
        ObjectPropertyAssertion(<http://x/r> <urn:q#a> <urn:q#b>)\n\
        DataPropertyAssertion(<http://x/u> <urn:q#a> \"1\"^^xsd:integer)\n\
        DataPropertyAssertion(<http://x/u> <urn:q#b> \"2\"^^xsd:integer)\n\
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
    for route in ROUTES {
        let answer = classify(text, route);
        assert_eq!(
            answer,
            Answer { consistent: true, dropped: 0, unsat: BTreeSet::new(), subs: expected.clone() },
            "route {route:?}"
        );
    }
}

/// The clause frontend never carries a negative data assertion: the positive
/// one still gives `E ⊑ D`, and a clause route counts the omitted axiom. The
/// automatic route may instead answer through the exact ground source
/// compilation, which carries the negative assertion as a complemented class
/// assertion (nothing dropped).
#[test]
fn negative_data_assertion_is_published_as_dropped() {
    let text = format!("{HEADER}{SINGLE}NegativeDataPropertyAssertion(:u :a \"2\"^^xsd:integer)\n)\n");
    for route in ROUTES {
        let answer = classify(&text, route);
        assert!(answer.consistent, "route {route:?}");
        if route.is_some() {
            assert_eq!(answer.dropped, 1, "route {route:?}");
        } else {
            assert!(answer.dropped <= 1, "route {route:?}");
        }
        assert_eq!(answer.subs, pairs(&[("E", "D")]), "route {route:?}");
    }
}

/// Above the literal-vocabulary cap (512) the assertions are carried through
/// the profiles the TBox observes (`frontend::literal_profiles`): the TBox
/// mentions only the token `1`, so `1` keeps its identity and the other 599
/// values share one representative. No construct counts values, so the
/// abstraction is exact: `E ⊑ D` with nothing dropped.
#[test]
fn assertions_above_the_literal_cap_are_carried_by_profile() {
    let mut text = format!(
        "{HEADER}SubClassOf(DataHasValue(:u \"1\"^^xsd:integer) :D)\nEquivalentClasses(:E ObjectOneOf(:a))\n"
    );
    for value in 1..=600 {
        text.push_str(&format!("DataPropertyAssertion(:u :a \"{value}\"^^xsd:integer)\n"));
    }
    text.push_str(")\n");
    for route in ROUTES {
        let answer = classify(&text, route);
        assert_eq!(
            answer,
            Answer { consistent: true, dropped: 0, unsat: BTreeSet::new(), subs: pairs(&[("E", "D")]) },
            "route {route:?}"
        );
    }
}

/// A data cardinality counts distinct values, which the profile abstraction
/// does not preserve: above the cap the conversion still declines and every
/// assertion is published as dropped. (The bound sits on a superproperty
/// and on a class with no instances, so the answer itself does not depend
/// on it.)
#[test]
fn counted_assertions_above_the_literal_cap_are_published_as_dropped() {
    let mut text = format!(
        "{HEADER}SubClassOf(DataHasValue(:u \"1\"^^xsd:integer) :D)\nEquivalentClasses(:E ObjectOneOf(:a))\n\
         Declaration(DataProperty(:w)) Declaration(Class(:Never)) SubDataPropertyOf(:u :w)\n\
         SubClassOf(:Never DataMaxCardinality(1 :w))\n"
    );
    for value in 1..=600 {
        text.push_str(&format!("DataPropertyAssertion(:u :a \"{value}\"^^xsd:integer)\n"));
    }
    text.push_str(")\n");
    for route in ROUTES {
        let answer = classify(&text, route);
        assert!(answer.consistent, "route {route:?}");
        assert_eq!(answer.dropped, 600, "route {route:?}");
    }
}

/// Profiles see the ranges the TBox mentions: among 600 values on 600
/// individuals, `b` (value 550) is in `D ≡ ∃u.integer[≥ 500]` and `c`
/// (value 3) is not. A string value under an integer range is a clash.
#[test]
fn profiles_preserve_facet_membership_and_range_clashes() {
    let mut text = format!(
        "{HEADER}Declaration(Class(:F)) Declaration(NamedIndividual(:b)) Declaration(NamedIndividual(:c))\n\
         EquivalentClasses(:D DataSomeValuesFrom(:u DatatypeRestriction(xsd:integer \
         xsd:minInclusive \"500\"^^xsd:integer)))\n\
         EquivalentClasses(:E ObjectOneOf(:b)) EquivalentClasses(:F ObjectOneOf(:c))\n\
         DataPropertyAssertion(:u :b \"550\"^^xsd:integer) DataPropertyAssertion(:u :c \"3\"^^xsd:integer)\n"
    );
    for value in 1..=600 {
        text.push_str(&format!("DataPropertyAssertion(:u <http://example.org/t#i{value}> \"{value}\"^^xsd:integer)\n"));
    }
    let consistent = format!("{text})\n");
    for route in ROUTES {
        let answer = classify(&consistent, route);
        assert_eq!(
            answer,
            Answer { consistent: true, dropped: 0, unsat: BTreeSet::new(), subs: pairs(&[("E", "D")]) },
            "route {route:?}"
        );
    }
    let clash = format!("{text}DataPropertyRange(:u xsd:integer)\n\
        DataPropertyAssertion(:u <http://example.org/t#s> \"x\"^^xsd:string)\n)\n");
    for route in ROUTES {
        assert!(!classify(&clash, route).consistent, "route {route:?}");
    }
}

/// The counterexample to a per-subject abstraction under counting: `a` and
/// `b` are identified through the functional object property `r`, and the
/// functional data property `u` then has two distinct values. It must stay
/// inconsistent; padded above the literal cap it must not be published as a
/// complete consistent answer.
#[test]
fn merged_individuals_keep_distinct_values_under_counting() {
    let body = "Declaration(ObjectProperty(:r)) Declaration(NamedIndividual(:x)) Declaration(NamedIndividual(:b))\n\
        FunctionalDataProperty(:u) FunctionalObjectProperty(:r)\n\
        ObjectPropertyAssertion(:r :x :a) ObjectPropertyAssertion(:r :x :b)\n\
        DataPropertyAssertion(:u :a \"1\"^^xsd:integer) DataPropertyAssertion(:u :b \"2\"^^xsd:integer)\n";
    let text = format!("{HEADER}{body})\n");
    for route in ROUTES {
        assert!(!classify(&text, route).consistent, "route {route:?}");
    }
    let mut padded = format!("{HEADER}{body}");
    for value in 3..=600 {
        padded.push_str(&format!("DataPropertyAssertion(:u <http://example.org/t#i{value}> \"{value}\"^^xsd:integer)\n"));
    }
    padded.push_str(")\n");
    for route in ROUTES {
        let answer = classify(&padded, route);
        assert!(!answer.consistent || answer.dropped > 0, "route {route:?}: {answer:?}");
    }
}

/// An inconsistency proved without the uncarried assertions is exact: adding
/// axioms cannot restore consistency, so nothing is reported as dropped.
#[test]
fn inconsistency_without_uncarried_assertions_reports_nothing_dropped() {
    let text = format!(
        "{HEADER}{SINGLE}NegativeDataPropertyAssertion(:u :a \"2\"^^xsd:integer)\n\
         ClassAssertion(owl:Nothing :a)\n)\n"
    );
    let answer = classify(&text, None);
    assert!(!answer.consistent);
    assert_eq!(answer.dropped, 0);
}
