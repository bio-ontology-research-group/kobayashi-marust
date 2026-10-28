//! OWL 2 keys are rewritten into the DL-safe rules they denote
//! (`frontend::has_key`) and reasoned over by the rule routes. Every expected
//! answer below is HermiT's (`classifier-hermit.jar`, HermiT 1.4).
use std::io::Read;
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

static NEXT: AtomicUsize = AtomicUsize::new(0);

struct Answer {
    consistent: bool,
    dropped: usize,
    subsumptions: Vec<(String, String)>,
}

/// `km classify --lines` on `text`; `None` when the route refuses the input.
fn classify(text: &str, route: Option<&str>) -> Option<Answer> {
    let path = std::env::temp_dir().join(format!(
        "km-has-key-{}-{}.ofn",
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
        return None;
    }
    let mut answer = Answer { consistent: true, dropped: usize::MAX, subsumptions: Vec::new() };
    for line in stdout.lines() {
        if let Some(v) = line.strip_prefix("CONSISTENT ") {
            answer.consistent = v.trim() == "1";
        } else if let Some(v) = line.strip_prefix("DROPPED ") {
            answer.dropped = v.trim().parse().unwrap();
        } else if let Some(v) = line.strip_prefix("SUB\t") {
            let (a, b) = v.split_once('\t').unwrap();
            answer.subsumptions.push((a.to_string(), b.to_string()));
        }
    }
    assert_ne!(answer.dropped, usize::MAX, "DROPPED line missing:\n{stdout}");
    Some(answer)
}

fn iri(name: &str) -> String {
    format!("<urn:t#{name}>")
}

/// Classes `A`, `B`, `Q`; object property `r`; data property `d`; named
/// individuals `a`, `b`, `c`, `e`. Full IRIs only.
fn ontology(axioms: &[String]) -> String {
    let mut declarations: Vec<String> = ["A", "B", "Q", "Pa", "Pb"]
        .iter()
        .map(|c| format!("Declaration(Class({}))", iri(c)))
        .collect();
    declarations.push(format!("Declaration(ObjectProperty({}))", iri("r")));
    declarations.push(format!("Declaration(DataProperty({}))", iri("d")));
    for i in ["a", "b", "c", "e"] {
        declarations.push(format!("Declaration(NamedIndividual({}))", iri(i)));
    }
    format!(
        "Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\nOntology(<urn:t>\n{}\n{}\n)\n",
        declarations.join("\n"),
        axioms.join("\n")
    )
}

fn class_assertion(class: &str, individual: &str) -> String {
    format!("ClassAssertion({class} {})", iri(individual))
}

/// `a` and `b` are both `A`; `a` is `B` and, when `clash`, `b` is `¬B`.
fn key_abox(clash: bool) -> Vec<String> {
    let mut axioms = vec![
        class_assertion(&iri("A"), "a"),
        class_assertion(&iri("A"), "b"),
        class_assertion(&iri("B"), "a"),
    ];
    if clash {
        axioms.push(class_assertion(&format!("ObjectComplementOf({})", iri("B")), "b"));
    }
    axioms
}

fn object_key() -> String {
    format!("HasKey({} ({}) ())", iri("A"), iri("r"))
}

fn data_key() -> String {
    format!("HasKey({} () ({}))", iri("A"), iri("d"))
}

fn data_values(a: &str, b: &str) -> Vec<String> {
    vec![
        format!("DataPropertyAssertion({} {} {a})", iri("d"), iri("a")),
        format!("DataPropertyAssertion({} {} {b})", iri("d"), iri("b")),
    ]
}

/// HermiT: inconsistent. `a` and `b` share the key value `c`, so `a = b`.
/// Without the clash HermiT finds it consistent.
#[test]
fn object_key_merges_named_individuals() {
    for clash in [true, false] {
        let mut axioms = vec![
            object_key(),
            format!("ObjectPropertyAssertion({} {} {})", iri("r"), iri("a"), iri("c")),
            format!("ObjectPropertyAssertion({} {} {})", iri("r"), iri("b"), iri("c")),
        ];
        axioms.extend(key_abox(clash));
        let answer = classify(&ontology(&axioms), None).expect("automatic answer");
        assert_eq!(answer.consistent, !clash, "clash {clash}");
        if !clash {
            assert_eq!(answer.dropped, 0);
        }
    }
}

/// OWL 2 keys compare data values, not spellings. HermiT: `"1"` equals
/// `"01"^^xsd:integer` and `"1.0"^^xsd:decimal` (inconsistent with the clash),
/// and differs from `"2"` (consistent).
#[test]
fn data_key_compares_values_not_spellings() {
    let one = "\"1\"^^xsd:integer";
    for (other, equal) in [
        ("\"1\"^^xsd:integer", true),
        ("\"01\"^^xsd:integer", true),
        ("\"1.0\"^^xsd:decimal", true),
        ("\"2\"^^xsd:integer", false),
    ] {
        for clash in [true, false] {
            let mut axioms = vec![data_key()];
            axioms.extend(data_values(one, other));
            axioms.extend(key_abox(clash));
            let answer = classify(&ontology(&axioms), None).expect("automatic answer");
            assert_eq!(answer.consistent, !(clash && equal), "{other}, clash {clash}");
            if answer.consistent {
                assert_eq!(answer.dropped, 0, "{other}, clash {clash}");
            }
        }
    }
}

/// A key constrains named individuals only. `b` has an anonymous `r`-successor
/// in `Q ⊑ A ⊓ ∃r.{c}` with `Q` disjoint from `B`; identifying it with the
/// named `a` (an `A` with `r(a, c)` and `B(a)`) would be a clash. HermiT:
/// consistent, `Q ⊑ A`, `Q` satisfiable. Asserting `Q(e)` for a named `e`
/// makes the key fire (`e = a`): HermiT inconsistent.
#[test]
fn key_ignores_anonymous_individuals() {
    let mut axioms = vec![
        object_key(),
        format!(
            "SubClassOf({} ObjectIntersectionOf({} ObjectHasValue({} {})))",
            iri("Q"), iri("A"), iri("r"), iri("c")
        ),
        format!("DisjointClasses({} {})", iri("Q"), iri("B")),
        class_assertion(&iri("A"), "a"),
        class_assertion(&iri("B"), "a"),
        format!("ObjectPropertyAssertion({} {} {})", iri("r"), iri("a"), iri("c")),
        class_assertion(&format!("ObjectSomeValuesFrom({} {})", iri("r"), iri("Q")), "b"),
    ];
    let answer = classify(&ontology(&axioms), None).expect("automatic answer");
    assert!(answer.consistent);
    assert_eq!(answer.dropped, 0);
    assert_eq!(answer.subsumptions, vec![("urn:t#Q".to_string(), "urn:t#A".to_string())]);
    axioms.push(class_assertion(&iri("Q"), "e"));
    let answer = classify(&ontology(&axioms), None).expect("automatic answer");
    assert!(!answer.consistent);
}

/// Every route either refuses a key, answers exactly, or counts what it
/// leaves out: never a consistent answer with `DROPPED 0` where HermiT
/// finds an inconsistency.
#[test]
fn no_route_publishes_a_lost_key_as_complete() {
    let mut object = vec![
        object_key(),
        format!("ObjectPropertyAssertion({} {} {})", iri("r"), iri("a"), iri("c")),
        format!("ObjectPropertyAssertion({} {} {})", iri("r"), iri("b"), iri("c")),
    ];
    object.extend(key_abox(true));
    let mut data = vec![data_key()];
    data.extend(data_values("\"1\"^^xsd:integer", "\"01\"^^xsd:integer"));
    data.extend(key_abox(true));
    for text in [ontology(&object), ontology(&data)] {
        for route in ["nominals", "certified_nominals", "default", "lean", "ht_general", "ht_rules", "ht_bridge"] {
            if let Some(answer) = classify(&text, Some(route)) {
                assert!(!answer.consistent || answer.dropped >= 1,
                    "{route}: consistent with DROPPED {}\n{text}", answer.dropped);
            }
        }
    }
}

/// The rule route checks consistency with the rules and then classifies
/// without them. That is exact only without nominals: here the key makes
/// `a = b` through facts stated with nominals, so `Pb ⊑ B` (HermiT: `Pa ≡ Pb`,
/// both under `A` and `B`). The route must either find it or count the rule.
#[test]
fn rule_route_counts_a_key_its_nominal_taxonomy_ignores() {
    let text = ontology(&[
        object_key(),
        format!("EquivalentClasses({} ObjectOneOf({}))", iri("Pa"), iri("a")),
        format!("EquivalentClasses({} ObjectOneOf({}))", iri("Pb"), iri("b")),
        format!("SubClassOf({} ObjectIntersectionOf({} {} ObjectHasValue({} {})))",
            iri("Pa"), iri("A"), iri("B"), iri("r"), iri("c")),
        format!("SubClassOf({} ObjectIntersectionOf({} ObjectHasValue({} {})))",
            iri("Pb"), iri("A"), iri("r"), iri("c")),
    ]);
    let expected = ("urn:t#Pb".to_string(), "urn:t#B".to_string());
    for route in [None, Some("ht_rules")] {
        let answer = classify(&text, route).expect("answer");
        assert!(answer.consistent);
        assert!(answer.subsumptions.contains(&expected) || answer.dropped > 0,
            "{route:?}: Pb ⊑ B missing with DROPPED 0");
    }
    let answer = classify(&text, None).expect("automatic answer");
    assert!(answer.subsumptions.contains(&expected) && answer.dropped == 0);
}

/// A data key reaches a nominal class query: HermiT `Pb ⊑ B` (the key value
/// `"01"` equals `1`, so `a = b`). The finite data-rule route classifies
/// without the rule, so it must count it.
#[test]
fn data_key_behind_a_nominal_query_is_found_or_counted() {
    let mut axioms = vec![
        data_key(),
        format!("EquivalentClasses({} ObjectOneOf({}))", iri("Pb"), iri("b")),
    ];
    axioms.extend(data_values("\"1\"^^xsd:integer", "\"01\"^^xsd:integer"));
    axioms.extend(key_abox(false));
    let answer = classify(&ontology(&axioms), None).expect("automatic answer");
    assert!(answer.consistent);
    let expected = ("urn:t#Pb".to_string(), "urn:t#B".to_string());
    assert!(answer.subsumptions.contains(&expected) || answer.dropped > 0,
        "Pb ⊑ B missing with DROPPED 0");
}
