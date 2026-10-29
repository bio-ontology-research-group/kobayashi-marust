//! Regression tests for provably empty and provably universal data ranges.
//!
//! `C ≡ DataSomeValuesFrom(d rdfs:Literal) ⊓ DataAllValuesFrom(d
//! DataComplementOf(rdfs:Literal))` is unsatisfiable, but every KM route
//! classified it as satisfiable: the frontend gave each data range its own
//! concept label, and no clause made the label of an empty range `⊥` or the
//! label of a universal range (`rdfs:Literal` and its boolean equivalents)
//! hold for every value. The same gap affected all restriction positions
//! (∃, ∀, min, max, exact, DataHasValue with ∀, DataPropertyRange) and
//! `owl:bottomDataProperty`.
//!
//! Each case builds a small ontology around one data range `R`, with
//! reference classes for the unqualified cardinalities, and compares KM's
//! complete answer (unsatisfiable classes and every named subsumption) with
//! the exact answer derived from the OWL 2 Direct Semantics. For these
//! ontologies that answer depends only on whether `R` is empty or universal:
//! an element is determined by its number of `d` values (0, 1 or at least 2),
//! whether one of them is `"1"^^xsd:integer`, and whether it has an `e`
//! value; `expected` enumerates those element types. HermiT 1.4.3.456 gives
//! the same answers, except for `DataIntersectionOf(xsd:integer xsd:string)`,
//! where it reports the satisfiable `DataMinCardinality(1 d)` as
//! unsatisfiable.
use std::collections::BTreeSet;
use std::io::Read;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

const BOUND: Duration = Duration::from_secs(30);
static NEXT: AtomicUsize = AtomicUsize::new(0);

struct Fixture(PathBuf);
impl Fixture {
    fn new(text: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "km-data-range-extent-{}-{}.ofn",
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
    unsat: BTreeSet<String>,
    subs: BTreeSet<(String, String)>,
}

/// Classify `text` with `km classify --lines` on `route` (`None` = the
/// default policy), killing the child (by its own handle) after `BOUND`.
/// Subsumptions involving unsatisfiable classes or builtins are dropped.
fn classify(text: &str, route: Option<&str>) -> Answer {
    classify_within(text, route, BOUND)
}

fn classify_within(text: &str, route: Option<&str>, bound: Duration) -> Answer {
    let stdout = run_within(text, route, bound);
    parse(&stdout)
}

/// Raw `km classify --lines` output.
fn run(text: &str, route: Option<&str>) -> String {
    run_within(text, route, BOUND)
}

fn run_within(text: &str, route: Option<&str>, bound: Duration) -> String {
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
            return stdout;
        }
        if started.elapsed() > bound {
            let _ = child.kill();
            let _ = child.wait();
            panic!("km classify exceeded {bound:?} on route {route:?}:\n{text}");
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
            [single] if single.starts_with("CONSISTENT ") => consistent = Some(single.ends_with(" 1")),
            ["UNSAT", class] => {
                unsat.insert(class.trim_start_matches(':').to_string());
            }
            ["SUB", sub, sup] => {
                subs.insert((sub.trim_start_matches(':').to_string(), sup.trim_start_matches(':').to_string()));
            }
            _ => {}
        }
    }
    assert_eq!(consistent, Some(true), "{stdout}");
    let subs = subs
        .into_iter()
        .filter(|(a, b)| a != b && !unsat.contains(a) && !unsat.contains(b))
        .filter(|(a, b)| !a.starts_with("owl:") && !b.starts_with("owl:"))
        .collect();
    Answer { unsat, subs }
}

const HEADER: &str = "Prefix(:=<http://example.org/t#>)\n\
    Prefix(owl:=<http://www.w3.org/2002/07/owl#>)\n\
    Prefix(rdfs:=<http://www.w3.org/2000/01/rdf-schema#>)\n\
    Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\n\
    Ontology(<http://example.org/t>\n\
    Declaration(DataProperty(:d)) Declaration(DataProperty(:e))\n";

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Extent {
    Empty,
    Universal,
}

/// Reference classes present in every ontology.
const REFERENCES: [(&str, &str); 4] = [
    ("Has", "DataMinCardinality(1 :d)"),
    ("Two", "DataMinCardinality(2 :d)"),
    ("No", "DataMaxCardinality(0 :d)"),
    ("AtMostOne", "DataMaxCardinality(1 :d)"),
];

/// The class under test for each restriction position of `R`.
const TARGETS: [(&str, &str); 13] = [
    ("Some", "DataSomeValuesFrom(:d R)"),
    ("All", "DataAllValuesFrom(:d R)"),
    ("Min1", "DataMinCardinality(1 :d R)"),
    ("Min2", "DataMinCardinality(2 :d R)"),
    ("Max0", "DataMaxCardinality(0 :d R)"),
    ("Max1", "DataMaxCardinality(1 :d R)"),
    ("Exact0", "DataExactCardinality(0 :d R)"),
    ("Exact1", "DataExactCardinality(1 :d R)"),
    ("SomeLitAllR", "ObjectIntersectionOf(DataSomeValuesFrom(:d rdfs:Literal) DataAllValuesFrom(:d R))"),
    ("HasValAllR", "ObjectIntersectionOf(DataHasValue(:d \"1\"^^xsd:integer) DataAllValuesFrom(:d R))"),
    ("NotSome", "ObjectComplementOf(DataSomeValuesFrom(:d R))"),
    ("NotAll", "ObjectComplementOf(DataAllValuesFrom(:d R))"),
    ("HasE", "DataMinCardinality(1 :e)"),
];

/// One ontology per restriction position: the references plus the target
/// (and, for `HasE`, `DataPropertyRange(:e R)` with a DataHasValue class).
fn ontology(range: &str, prelude: &str, target: &str) -> String {
    let mut classes: Vec<(&str, String)> =
        REFERENCES.iter().map(|(name, expr)| (*name, expr.to_string())).collect();
    let expr = TARGETS.iter().find(|(name, _)| *name == target).unwrap().1;
    classes.push((target, expr.replace(" R)", &format!(" {range})"))));
    let mut axioms = prelude.to_string();
    if target == "HasE" {
        classes.push(("HasEval", "DataHasValue(:e \"1\"^^xsd:integer)".to_string()));
        axioms.push_str(&format!("DataPropertyRange(:e {range})\n"));
    }
    let mut text = HEADER.to_string();
    for (name, expr) in &classes {
        text.push_str(&format!("Declaration(Class(:{name})) EquivalentClasses(:{name} {expr})\n"));
    }
    text.push_str(&axioms);
    text.push_str(")\n");
    text
}

/// Exact answer for the classes `present`, by enumerating element types.
fn expected(extent: Extent, present: &[&str]) -> Answer {
    let mut types: Vec<Vec<(&str, bool)>> = Vec::new();
    for n in 0..3usize {
        for has_one in [false, true] {
            for e_values in [false, true] {
                for e_one in [false, true] {
                    if (has_one && n == 0) || (e_one && !e_values) {
                        continue;
                    }
                    if extent == Extent::Empty && e_values {
                        continue; // DataPropertyRange(:e R) with R empty
                    }
                    let in_range = if extent == Extent::Empty { 0 } else { n };
                    let all = in_range == n;
                    types.push(vec![
                        ("Has", n >= 1), ("Two", n >= 2), ("No", n == 0), ("AtMostOne", n <= 1),
                        ("Some", in_range >= 1), ("All", all),
                        ("Min1", in_range >= 1), ("Min2", in_range >= 2),
                        ("Max0", in_range == 0), ("Max1", in_range <= 1),
                        ("Exact0", in_range == 0), ("Exact1", in_range == 1),
                        ("SomeLitAllR", n >= 1 && all),
                        // "1"^^xsd:integer lies in R only when R is universal.
                        ("HasValAllR", has_one && all && extent == Extent::Universal),
                        ("NotSome", in_range == 0), ("NotAll", !all),
                        ("HasE", e_values), ("HasEval", e_one),
                    ]);
                }
            }
        }
    }
    let holds = |t: &Vec<(&str, bool)>, class: &str| t.iter().find(|(n, _)| *n == class).unwrap().1;
    let unsat: BTreeSet<String> = present
        .iter()
        .filter(|class| !types.iter().any(|t| holds(t, class)))
        .map(|class| class.to_string())
        .collect();
    let mut subs = BTreeSet::new();
    for sub in present {
        for sup in present {
            if sub != sup && !unsat.contains(*sub) && !unsat.contains(*sup)
                && types.iter().filter(|t| holds(t, sub)).all(|t| holds(t, sup))
            {
                subs.insert((sub.to_string(), sup.to_string()));
            }
        }
    }
    Answer { unsat, subs }
}

fn check_family(range: &str, prelude: &str, extent: Extent, routes: &[Option<&str>]) {
    for (target, _) in TARGETS {
        let text = ontology(range, prelude, target);
        let mut present: Vec<&str> = REFERENCES.iter().map(|(name, _)| *name).collect();
        present.push(target);
        if target == "HasE" {
            present.push("HasEval");
        }
        let want = expected(extent, &present);
        for route in routes {
            assert_eq!(classify(&text, *route), want, "range {range}, target {target}, route {route:?}");
        }
    }
}

/// The reported reproducer, on the default policy and on the explicit
/// routes that answer it (others decline with "unsupported").
#[test]
fn literal_existential_with_universal_complement_of_literal_is_unsatisfiable() {
    let text = format!(
        "{HEADER}Declaration(Class(:C)) Declaration(Class(:D))\n\
         EquivalentClasses(:C ObjectIntersectionOf(DataSomeValuesFrom(:d rdfs:Literal) \
         DataAllValuesFrom(:d DataComplementOf(rdfs:Literal))))\n\
         SubClassOf(:D :C)\n)\n"
    );
    let want = Answer { unsat: ["C", "D"].iter().map(|c| c.to_string()).collect(), subs: BTreeSet::new() };
    for route in ROUTES {
        assert_eq!(classify(&text, *route), want, "route {route:?}");
    }
}

/// Routes checked for the reproducer, the two original spellings and
/// `owl:bottomDataProperty`: the default policy and one route of each calculus
/// family that accepts all of these inputs. (Routes outside their fragment
/// decline with "unsupported"; `ht_bridge` and `certified_card_nominals`
/// decline the `DataPropertyRange`/`DataHasValue` cases.)
const ROUTES: &[Option<&str>] = &[
    None,
    Some("cb_plain1"),
    Some("cb_absorb8"),
    Some("certified_el_production"),
    Some("ht_general"),
    Some("lean"),
    Some("tableau"),
    Some("nominals"),
];

const EMPTY_RANGES: [&str; 8] = [
    "DataComplementOf(rdfs:Literal)",
    "DataIntersectionOf(xsd:integer xsd:string)",
    "DataIntersectionOf(xsd:integer DataComplementOf(xsd:integer))",
    "DatatypeRestriction(xsd:integer xsd:minInclusive \"5\"^^xsd:integer xsd:maxInclusive \"3\"^^xsd:integer)",
    "DataIntersectionOf(DataOneOf(\"1\"^^xsd:integer) DataOneOf(\"2\"^^xsd:integer))",
    "DataComplementOf(DataUnionOf(xsd:string DataComplementOf(xsd:string)))",
    "DataUnionOf(DataComplementOf(rdfs:Literal) DataIntersectionOf(xsd:boolean xsd:integer))",
    "DataIntersectionOf(xsd:boolean DataComplementOf(DataOneOf(\"true\"^^xsd:boolean \"false\"^^xsd:boolean)))",
];

const UNIVERSAL_RANGES: [&str; 5] = [
    "rdfs:Literal",
    "DataComplementOf(DataComplementOf(rdfs:Literal))",
    "DataUnionOf(xsd:integer DataComplementOf(xsd:integer))",
    "DataComplementOf(DataIntersectionOf(xsd:integer xsd:string))",
    "DataUnionOf(xsd:string rdfs:Literal)",
];

#[test]
fn empty_data_ranges_in_every_position() {
    for range in EMPTY_RANGES {
        check_family(range, "", Extent::Empty, &[None]);
    }
}

#[test]
fn universal_data_ranges_in_every_position() {
    for range in UNIVERSAL_RANGES {
        check_family(range, "", Extent::Universal, &[None]);
    }
}

/// A user datatype defined as an empty or universal range behaves like it.
#[test]
fn datatype_definitions_of_empty_and_universal_ranges() {
    check_family(
        ":Empty",
        "Declaration(Datatype(:Empty)) DatatypeDefinition(:Empty DataComplementOf(rdfs:Literal))\n",
        Extent::Empty,
        &[None],
    );
    check_family(
        ":Full",
        "Declaration(Datatype(:Full)) \
         DatatypeDefinition(:Full DataUnionOf(xsd:string DataComplementOf(xsd:string)))\n",
        Extent::Universal,
        &[None],
    );
}

/// The two spellings that started the report, on every listed route.
#[test]
fn complement_of_literal_and_literal_on_every_route() {
    check_family("DataComplementOf(rdfs:Literal)", "", Extent::Empty, ROUTES);
    check_family("rdfs:Literal", "", Extent::Universal, ROUTES);
}

/// `owl:bottomDataProperty` has no values: restrictions forcing a value of it
/// (or of a subproperty) are unsatisfiable; `∀`/`≤` restrictions are `⊤`.
#[test]
fn bottom_data_property_has_no_values() {
    let text = format!(
        "{HEADER}Declaration(DataProperty(:f))\n\
         Declaration(Class(:Bs)) EquivalentClasses(:Bs DataSomeValuesFrom(owl:bottomDataProperty rdfs:Literal))\n\
         Declaration(Class(:Bm)) EquivalentClasses(:Bm DataMinCardinality(1 owl:bottomDataProperty))\n\
         Declaration(Class(:Bv)) EquivalentClasses(:Bv DataHasValue(owl:bottomDataProperty \"1\"^^xsd:integer))\n\
         Declaration(Class(:Ball)) EquivalentClasses(:Ball DataAllValuesFrom(owl:bottomDataProperty xsd:string))\n\
         Declaration(Class(:Bmax)) EquivalentClasses(:Bmax DataMaxCardinality(0 owl:bottomDataProperty))\n\
         SubDataPropertyOf(:f owl:bottomDataProperty)\n\
         Declaration(Class(:Fs)) EquivalentClasses(:Fs DataSomeValuesFrom(:f xsd:integer))\n\
         Declaration(Class(:Fa)) EquivalentClasses(:Fa DataAllValuesFrom(:f xsd:string))\n\
         Declaration(Class(:A)) SubClassOf(:A DataHasValue(:d \"1\"^^xsd:integer))\n)\n"
    );
    let top = ["Ball", "Bmax", "Fa"];
    let mut subs = BTreeSet::new();
    for sub in ["A", "Ball", "Bmax", "Fa"] {
        for sup in top {
            if sub != sup {
                subs.insert((sub.to_string(), sup.to_string()));
            }
        }
    }
    let want = Answer { unsat: ["Bm", "Bs", "Bv", "Fs"].iter().map(|c| c.to_string()).collect(), subs };
    for route in ROUTES {
        assert_eq!(classify(&text, *route), want, "route {route:?}");
    }
}

/// Assertions that need a value in an empty range, or a value of
/// `owl:bottomDataProperty`, make the ontology inconsistent.
#[test]
fn assertions_against_empty_ranges_are_inconsistent() {
    let individual = "Declaration(NamedIndividual(:a))\n";
    for body in [
        "DataPropertyAssertion(owl:bottomDataProperty :a \"1\"^^xsd:integer)",
        "SubDataPropertyOf(:e owl:bottomDataProperty) DataPropertyAssertion(:e :a \"1\"^^xsd:integer)",
        "DataPropertyRange(:e DataComplementOf(rdfs:Literal)) DataPropertyAssertion(:e :a \"1\"^^xsd:integer)",
        "DataPropertyRange(:e DataIntersectionOf(xsd:integer xsd:string)) DataPropertyAssertion(:e :a \"x\")",
        "Declaration(Datatype(:E)) DatatypeDefinition(:E DataComplementOf(rdfs:Literal)) \
         DataPropertyRange(:e :E) DataPropertyAssertion(:e :a \"1\"^^xsd:integer)",
        "ClassAssertion(DataAllValuesFrom(:d DataIntersectionOf(xsd:integer xsd:string)) :a) \
         DataPropertyAssertion(:d :a \"x\")",
        "ClassAssertion(DataSomeValuesFrom(:d DataComplementOf(rdfs:Literal)) :a)",
        "SubClassOf(owl:Thing DataSomeValuesFrom(:d DataComplementOf(rdfs:Literal)))",
        "ClassAssertion(DataAllValuesFrom(:d rdfs:Literal) :a) ClassAssertion(ObjectComplementOf(\
         DataAllValuesFrom(:d DataComplementOf(DataComplementOf(rdfs:Literal)))) :a)",
    ] {
        let text = format!("{HEADER}{individual}{body}\n)\n");
        let stdout = run(&text, None);
        assert!(stdout.lines().any(|line| line == "CONSISTENT 0"), "{body}\n{stdout}");
    }
    // Control: a value outside a non-empty complex range only.
    let text = format!(
        "{HEADER}{individual}DataPropertyRange(:e DataComplementOf(xsd:string)) \
         DataPropertyAssertion(:e :a \"1\"^^xsd:integer)\n)\n"
    );
    assert!(run(&text, None).lines().any(|line| line == "CONSISTENT 1"));
}

/// Complements of non-trivial ranges relate to their operands: `¬D ∩ D = ∅`,
/// `¬¬D = D`, `x ⊑ ¬D` when `x ∩ D = ∅`, `¬D ⊑ ¬E` when `E ⊑ D`, and a
/// finite range minus each of its values is empty. Expected answers are hand
/// derived and agree with HermiT.
#[test]
fn complements_of_ordinary_ranges() {
    let names = |list: &[&str]| list.iter().map(|c| c.to_string()).collect::<BTreeSet<_>>();
    let pairs = |list: &[(&str, &str)]| {
        list.iter().map(|(a, b)| (a.to_string(), b.to_string())).collect::<BTreeSet<_>>()
    };
    let cases: &[(&str, &[(&str, &str)], &[&str])] = &[
        ("EquivalentClasses(:C DataSomeValuesFrom(:d DataIntersectionOf(DatatypeRestriction(xsd:integer \
          xsd:minInclusive \"1\"^^xsd:integer xsd:maxInclusive \"2\"^^xsd:integer) \
          DataComplementOf(DataOneOf(\"1\"^^xsd:integer)) DataComplementOf(DataOneOf(\"2\"^^xsd:integer)))))",
         &[], &["C"]),
        ("EquivalentClasses(:C ObjectIntersectionOf(DataMinCardinality(1 :d) \
          DataAllValuesFrom(:d DataComplementOf(xsd:integer)) \
          DataAllValuesFrom(:d DataComplementOf(DataComplementOf(xsd:integer)))))",
         &[], &["C"]),
        ("EquivalentClasses(:C ObjectIntersectionOf(DataSomeValuesFrom(:d DataComplementOf(xsd:integer)) \
          DataAllValuesFrom(:d xsd:integer)))",
         &[], &["C"]),
        ("EquivalentClasses(:X DataAllValuesFrom(:d xsd:integer)) \
          EquivalentClasses(:Y DataAllValuesFrom(:d DataComplementOf(DataComplementOf(xsd:integer))))",
         &[("X", "Y"), ("Y", "X")], &[]),
        ("EquivalentClasses(:X DataSomeValuesFrom(:d xsd:string)) \
          EquivalentClasses(:Y DataSomeValuesFrom(:d DataComplementOf(xsd:integer)))",
         &[("X", "Y")], &[]),
        ("EquivalentClasses(:X DataSomeValuesFrom(:d DataComplementOf(xsd:decimal))) \
          EquivalentClasses(:Y DataSomeValuesFrom(:d DataComplementOf(xsd:integer)))",
         &[("X", "Y")], &[]),
    ];
    for (body, subs, unsat) in cases {
        let text = format!(
            "{HEADER}Declaration(Class(:C)) Declaration(Class(:X)) Declaration(Class(:Y))\n{body}\n)\n"
        );
        // The tableau route declines facet and string ranges.
        for route in ROUTES.iter().filter(|route| **route != Some("tableau")) {
            let answer = classify(&text, *route);
            assert_eq!(answer, Answer { unsat: names(unsat), subs: pairs(subs) }, "{body} on {route:?}");
        }
    }
}

/// Every data value lies in `R` or in `DataComplementOf(R)`. The frontend
/// emits that excluded middle for every complement range that occurs (next
/// to the disjointness of the two), so restrictions over `R` and `¬R` relate
/// to the unqualified cardinalities. Expected answers are hand derived and
/// agree with HermiT 1.4.3.456.
#[test]
fn excluded_middle_of_complement_ranges() {
    let names = |list: &[&str]| list.iter().map(|c| c.to_string()).collect::<BTreeSet<_>>();
    let pairs = |list: &[(&str, &str)]| {
        list.iter().map(|(a, b)| (a.to_string(), b.to_string())).collect::<BTreeSet<_>>()
    };
    let one = "\"1\"^^xsd:integer";
    let has = "EquivalentClasses(:H DataMinCardinality(1 :d))";
    let none = "EquivalentClasses(:N DataMaxCardinality(0 :d))";
    let c_h = [("C", "H"), ("H", "C")];
    let c_n = [("C", "N"), ("N", "C")];
    let cases: Vec<(String, &[(&str, &str)])> = vec![
        // A ⊑ ∃d.Literal and C ≡ (d value 1) ⊔ ∃d.¬{1}: A ⊑ C.
        (format!("SubClassOf(:A DataSomeValuesFrom(:d rdfs:Literal)) \
          EquivalentClasses(:C ObjectUnionOf(DataHasValue(:d {one}) \
          DataSomeValuesFrom(:d DataComplementOf(DataOneOf({one})))))"), &[("A", "C")]),
        // ∃d.R ⊔ ∃d.¬R ≡ ≥1 d.
        (format!("{has} EquivalentClasses(:C ObjectUnionOf(DataSomeValuesFrom(:d xsd:integer) \
          DataSomeValuesFrom(:d DataComplementOf(xsd:integer))))"), &c_h),
        // ∀d.R ⊓ ∀d.¬R ≡ ≤0 d.
        (format!("{none} EquivalentClasses(:C ObjectIntersectionOf(DataAllValuesFrom(:d xsd:integer) \
          DataAllValuesFrom(:d DataComplementOf(xsd:integer))))"), &c_n),
        // ∃d.(R ⊔ ¬R) ≡ ≥1 d.
        (format!("{has} EquivalentClasses(:C DataSomeValuesFrom(:d \
          DataUnionOf(xsd:integer DataComplementOf(xsd:integer))))"), &c_h),
        // Nested: ∃d.¬¬R ⊔ ∃d.¬R ≡ ≥1 d.
        (format!("{has} EquivalentClasses(:C ObjectUnionOf(\
          DataSomeValuesFrom(:d DataComplementOf(DataComplementOf(xsd:integer))) \
          DataSomeValuesFrom(:d DataComplementOf(xsd:integer))))"), &c_h),
        // Value and complement of value: ∀d.{1} ⊓ ∀d.¬{1} ≡ ≤0 d.
        (format!("{none} EquivalentClasses(:C ObjectIntersectionOf(DataAllValuesFrom(:d DataOneOf({one})) \
          DataAllValuesFrom(:d DataComplementOf(DataOneOf({one})))))"), &c_n),
        // A facet range and its complement.
        (format!("{has} EquivalentClasses(:C ObjectUnionOf(\
          DataSomeValuesFrom(:d DatatypeRestriction(xsd:integer xsd:minInclusive {one})) \
          DataSomeValuesFrom(:d DataComplementOf(DatatypeRestriction(xsd:integer xsd:minInclusive {one})))))"), &c_h),
        // ∀d.¬¬R ⊓ ∀d.¬R ≡ ≤0 d.
        (format!("{none} EquivalentClasses(:C ObjectIntersectionOf(\
          DataAllValuesFrom(:d DataComplementOf(DataComplementOf(xsd:integer))) \
          DataAllValuesFrom(:d DataComplementOf(xsd:integer))))"), &c_n),
        // The pre-existing excluded middle of ¬(d value 1): ∀d.{1} ⊓ ¬(d value 1) ≡ ≤0 d.
        (format!("{none} EquivalentClasses(:C ObjectIntersectionOf(DataAllValuesFrom(:d DataOneOf({one})) \
          ObjectComplementOf(DataHasValue(:d {one}))))"), &c_n),
    ];
    for (body, subs) in &cases {
        let text = format!(
            "{HEADER}Declaration(Class(:A)) Declaration(Class(:C)) Declaration(Class(:H)) \
             Declaration(Class(:N))\n{body}\n)\n"
        );
        // The tableau route declines the union range. (`ht_general` missed
        // the excluded middle of two data ranges until its subset blocking
        // learned that a gained data-range label at a successor can enable a
        // recognition clause; docs/HYBRID-CB-HT.md section 8.) The forced
        // `nominals` arm is left out for the
        // value cases: on an individual-free input it instantiates the
        // unrelativized excluded middle at the data-value individual and runs
        // for minutes (as it already did for `ObjectComplementOf(DataHasValue)`).
        for route in ROUTES.iter().filter(|route| {
            !(**route == Some("tableau") && body.contains("DataUnionOf"))
                && !(**route == Some("nominals") && body.contains("DataOneOf"))
        }) {
            // The value cases split on the value singleton in every context
            // and take about 30 s on the CB routes, as the pre-existing
            // `ObjectComplementOf(DataHasValue)` case already did.
            let answer = classify_within(&text, *route, Duration::from_secs(180));
            assert_eq!(answer, Answer { unsat: names(&[]), subs: pairs(subs) }, "{body} on {route:?}");
        }
    }
}

/// Contraposition through complemented cardinality definers: `Two ⊑ Has`
/// entails `¬Has ⊑ ¬Two`. The HT translation folded each complement pair
/// `No ≡ ¬Has` into a negative body literal `¬Has`, which the worker matches
/// only against an explicit `¬Has` label, so `ht_general` and `tableau` missed
/// `No ⊑ AtMostOne` (docs/HYBRID-CB-HT.md section 7). The object-property and
/// cardinality-free spellings (the last with `T2` making `Two` Horn-derivable)
/// had the same miss.
#[test]
fn complemented_cardinality_definers_contrapose_on_every_route() {
    let classes = "Declaration(Class(:Has)) Declaration(Class(:Two)) Declaration(Class(:No)) \
                   Declaration(Class(:AtMostOne))\n\
                   EquivalentClasses(:No ObjectComplementOf(:Has))\n\
                   EquivalentClasses(:AtMostOne ObjectComplementOf(:Two))\n";
    let cases = [
        format!("{HEADER}{classes}EquivalentClasses(:Has DataMinCardinality(1 :d))\n\
                 EquivalentClasses(:Two DataMinCardinality(2 :d))\n)\n"),
        format!("{HEADER}Declaration(ObjectProperty(:r))\n{classes}\
                 EquivalentClasses(:Has ObjectMinCardinality(1 :r))\n\
                 EquivalentClasses(:Two ObjectMinCardinality(2 :r))\n)\n"),
        format!("{HEADER}Declaration(Class(:T2))\n{classes}SubClassOf(:Two :Has) SubClassOf(:T2 :Two)\n)\n"),
    ];
    let base = [("No", "AtMostOne"), ("Two", "Has")];
    for (i, text) in cases.iter().enumerate() {
        let mut subs = base.to_vec();
        if i == 2 {
            subs.extend([("T2", "Two"), ("T2", "Has")]);
        }
        let want = Answer {
            unsat: BTreeSet::new(),
            subs: subs.iter().map(|(a, b)| (a.to_string(), b.to_string())).collect(),
        };
        for route in ROUTES {
            assert_eq!(classify(text, *route), want, "case {i}, route {route:?}");
        }
    }
}
