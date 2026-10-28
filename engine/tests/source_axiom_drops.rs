//! Source axioms the clause set does not represent must reach the published
//! `DROPPED` count of a consistent answer on every route. Dropping a key, a
//! negative data assertion or an unread DL-safe rule never invents a
//! consequence, but it can lose an inconsistency, and an inconsistent
//! ontology entails every subsumption: a consistent answer without the count
//! would be published as complete when it is not.
use std::io::Read;
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

static NEXT: AtomicUsize = AtomicUsize::new(0);

/// `(consistent, dropped)` of `km classify --lines` on `text` and `route`.
fn classify(text: &str, route: Option<&str>) -> Option<(bool, usize)> {
    let path = std::env::temp_dir().join(format!(
        "km-source-drops-{}-{}.ofn",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::write(&path, text).unwrap();
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars_os() {
        if key.to_string_lossy().starts_with("KM_") {
            command.env_remove(key);
        }
    }
    if let Some(route) = route {
        command.env("KM_ROUTE", route);
    }
    command.args(["classify", "--lines"]).arg(&path).stdout(Stdio::piped()).stderr(Stdio::null());
    let started = Instant::now();
    let mut child = command.spawn().unwrap();
    let status = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break status;
        }
        if started.elapsed() > Duration::from_secs(60) {
            let _ = child.kill();
            let _ = child.wait();
            panic!("km classify exceeded 60 s");
        }
        std::thread::sleep(Duration::from_millis(20));
    };
    let mut stdout = String::new();
    child.stdout.take().unwrap().read_to_string(&mut stdout).unwrap();
    let _ = std::fs::remove_file(&path);
    if !status.success() {
        return None; // the route refused the input
    }
    let mut consistent = None;
    let mut dropped = None;
    for line in stdout.lines() {
        if let Some(v) = line.strip_prefix("CONSISTENT ") {
            consistent = Some(v.trim() == "1");
        }
        if let Some(v) = line.strip_prefix("DROPPED ") {
            dropped = v.trim().parse().ok();
        }
    }
    Some((consistent.expect("CONSISTENT line"), dropped.expect("DROPPED line")))
}

const ROUTES: [Option<&str>; 4] = [None, Some("nominals"), Some("certified_nominals"), Some("default")];

/// Keys are not encoded. HermiT: inconsistent (both individuals carry the
/// key value 1, so they are equal, but one is `A` and the other `¬A`).
#[test]
fn has_key_is_counted_as_dropped() {
    let text = "Prefix(:=<http://e.org/k#>)\nPrefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\n\
        Ontology(<http://e.org/k>\n\
        Declaration(Class(:C)) Declaration(Class(:A)) Declaration(DataProperty(:id))\n\
        Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))\n\
        HasKey(:C () (:id))\n\
        ClassAssertion(:C :a) ClassAssertion(:C :b)\n\
        DataPropertyAssertion(:id :a \"1\"^^xsd:integer) DataPropertyAssertion(:id :b \"1\"^^xsd:integer)\n\
        ClassAssertion(:A :a) ClassAssertion(ObjectComplementOf(:A) :b)\n)\n";
    for route in ROUTES {
        let (consistent, dropped) = classify(text, route).expect("answer");
        assert!(!consistent || dropped >= 1, "{route:?}: consistent with DROPPED {dropped}");
    }
}

/// A DL-safe rule with an unsupported built-in is refused by the automatic
/// route; a selected route that does not read rules must count it.
#[test]
fn unread_dl_safe_rule_is_counted_as_dropped() {
    let text = "Prefix(:=<http://e.org/r#>)\nOntology(<http://e.org/r>\n\
        Declaration(Class(:C)) Declaration(Class(:A)) Declaration(NamedIndividual(:a))\n\
        ClassAssertion(:C :a) ClassAssertion(ObjectComplementOf(:A) :a)\n\
        DLSafeRule(Body(ClassAtom(:C Variable(<urn:x>)) \
        BuiltInAtom(<http://www.w3.org/2003/11/swrlb#unknownThing> Variable(<urn:x>))) \
        Head(ClassAtom(:A Variable(<urn:x>))))\n)\n";
    for route in ROUTES {
        if let Some((consistent, dropped)) = classify(text, route) {
            assert!(!consistent || dropped >= 1, "{route:?}: consistent with DROPPED {dropped}");
        }
    }
}

/// `NegativeDataPropertyAssertion` contradicting a positive one: the
/// automatic route proves the inconsistency; a selected route that cannot
/// must count the negative assertion once (not twice).
#[test]
fn negative_data_assertion_is_counted_once() {
    let text = "Prefix(:=<http://e.org/n#>)\nPrefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\n\
        Ontology(<http://e.org/n>\n\
        Declaration(DataProperty(:id)) Declaration(NamedIndividual(:a))\n\
        DataPropertyAssertion(:id :a \"1\"^^xsd:integer) \
        NegativeDataPropertyAssertion(:id :a \"1\"^^xsd:integer)\n)\n";
    // A nominal route carries the positive assertion; a non-nominal one also
    // counts it (its individual has no proxy).
    for route in [Some("nominals"), Some("certified_nominals")] {
        let (consistent, dropped) = classify(text, route).expect("answer");
        if consistent {
            assert_eq!(dropped, 1, "{route:?}");
        }
    }
    let (consistent, dropped) = classify(text, Some("default")).expect("answer");
    assert!(!consistent || dropped >= 1);
    assert_eq!(classify(text, None), Some((false, 0)));
}

/// Annotation-property axioms are entailment-neutral and not counted.
#[test]
fn annotation_property_axioms_are_neutral() {
    let text = "Prefix(:=<http://e.org/p#>)\nOntology(<http://e.org/p>\n\
        Declaration(Class(:C)) Declaration(AnnotationProperty(:p)) Declaration(AnnotationProperty(:q))\n\
        SubAnnotationPropertyOf(:p :q) AnnotationPropertyDomain(:p :C) AnnotationPropertyRange(:p :C)\n)\n";
    for route in ROUTES {
        assert_eq!(classify(text, route), Some((true, 0)), "{route:?}");
    }
}

/// Outside nominal clausification the ground ABox enters the clause set only
/// through nominal proxies; equalities, inequalities and negative role
/// assertions are not represented there. A selected non-nominal route must
/// count them; the automatic route proves each inconsistency.
#[test]
fn abox_equality_and_negation_are_counted_on_selected_routes() {
    let cases = [
        "Prefix(:=<http://e.org/s#>)\nOntology(<http://e.org/s>\n\
         Declaration(Class(:A)) Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))\n\
         SameIndividual(:a :b) ClassAssertion(:A :a) ClassAssertion(ObjectComplementOf(:A) :b)\n)\n",
        "Prefix(:=<http://e.org/d#>)\nOntology(<http://e.org/d>\n\
         Declaration(Class(:A)) Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))\n\
         DifferentIndividuals(:a :b) EquivalentClasses(ObjectOneOf(:a) ObjectOneOf(:b))\n)\n",
        "Prefix(:=<http://e.org/o#>)\nOntology(<http://e.org/o>\n\
         Declaration(Class(:A)) Declaration(ObjectProperty(:r))\n\
         Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))\n\
         ClassAssertion(:A :a) SubClassOf(:A ObjectHasValue(:r :b)) NegativeObjectPropertyAssertion(:r :a :b)\n)\n",
    ];
    for text in cases {
        assert_eq!(classify(text, None), Some((false, 0)), "{text}");
        for route in ["default", "lean", "ht_general", "cb_plain1"] {
            if let Some((consistent, dropped)) = classify(text, Some(route)) {
                assert!(!consistent || dropped >= 1, "{route}: consistent with DROPPED {dropped}\n{text}");
            }
        }
    }
}
