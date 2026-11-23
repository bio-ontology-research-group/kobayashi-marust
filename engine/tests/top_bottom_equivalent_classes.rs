//! Classes equivalent to owl:Thing or owl:Nothing through data ranges,
//! object restrictions and nominals, on every route.
//!
//! The certified EL arm of the production portfolio published every class of
//! `range(d) ⊆ (<0)`, `Q ≡ ¬(d value 0)` without `X ⊑ Q`: one repair pass kept
//! the classes alive with an edge to a dead witness (tbox sweep
//! data20097_0008). Each case here has `A ⊑ B`, a class `C` in no axiom and a
//! query class `Q`. A `t_` case makes `Q` equivalent to owl:Thing, so every
//! class is below `Q`; a `b_` case makes `Q` empty. HermiT 1.4.3.456 gives the
//! same answers. A route may decline a case (exit 3); any answer it publishes
//! must be exact.
use std::collections::BTreeSet;
use std::io::Read;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

const BOUND: Duration = Duration::from_secs(60);
static NEXT: AtomicUsize = AtomicUsize::new(0);

const ROUTES: &[Option<&str>] = &[
    None,
    Some("production_all"),
    Some("cb_plain1"),
    Some("cb_absorb1"),
    Some("lean"),
    Some("certified_nominals"),
    Some("nominals"),
    Some("certified_card_nominals"),
    Some("certified_card_proxy_abox"),
    Some("elc"),
    Some("ht_bridge"),
];

const CASES: &[(&str, bool, &str)] = &[
    ("b_data_has", false, r#"DataPropertyRange(:d DatatypeRestriction(xsd:integer xsd:maxExclusive "0"^^xsd:integer))
EquivalentClasses(:Q DataHasValue(:d "0"^^xsd:integer))"#),
    ("b_data_min", false, r#"FunctionalDataProperty(:d)
EquivalentClasses(:Q DataMinCardinality(2 :d))"#),
    ("b_data_some", false, r#"DataPropertyRange(:d xsd:string)
EquivalentClasses(:Q DataSomeValuesFrom(:d xsd:integer))"#),
    ("b_nom_diff", false, r#"DifferentIndividuals(:a :b)
EquivalentClasses(:Q ObjectIntersectionOf(ObjectOneOf(:a) ObjectOneOf(:b)))"#),
    ("b_nom_empty", false, r#"ClassAssertion(ObjectComplementOf(:C) :a)
EquivalentClasses(:Q ObjectIntersectionOf(ObjectOneOf(:a) :C))"#),
    ("b_obj_disj", false, r#"SubClassOf(owl:Thing ObjectAllValuesFrom(:r :C))
EquivalentClasses(:Q ObjectSomeValuesFrom(:r ObjectComplementOf(:C)))"#),
    ("b_obj_min", false, r#"FunctionalObjectProperty(:r)
EquivalentClasses(:Q ObjectMinCardinality(2 :r))"#),
    ("b_obj_some", false, r#"ObjectPropertyRange(:r :C)
EquivalentClasses(:Q ObjectSomeValuesFrom(:r ObjectComplementOf(:C)))"#),
    ("t_data_all", true, r#"DataPropertyRange(:d xsd:integer)
EquivalentClasses(:Q DataAllValuesFrom(:d xsd:integer))"#),
    ("t_data_max", true, r#"FunctionalDataProperty(:d)
EquivalentClasses(:Q DataMaxCardinality(1 :d))"#),
    ("t_data_neghas", true, r#"DataPropertyRange(:d DatatypeRestriction(xsd:integer xsd:maxExclusive "0"^^xsd:integer))
EquivalentClasses(:Q ObjectComplementOf(DataHasValue(:d "0"^^xsd:integer)))"#),
    ("t_data_negsome", true, r#"DataPropertyRange(:d xsd:string)
EquivalentClasses(:Q ObjectComplementOf(DataSomeValuesFrom(:d xsd:integer)))"#),
    ("t_data_unionrange", true, r#"EquivalentClasses(:Q ObjectUnionOf(DataSomeValuesFrom(:d rdfs:Literal) ObjectComplementOf(DataSomeValuesFrom(:d rdfs:Literal))))"#),
    ("t_nom_cover", true, r#"SubClassOf(owl:Thing ObjectOneOf(:a :b))
EquivalentClasses(:Q ObjectOneOf(:a :b))"#),
    ("t_nom_hasvalue", true, r#"SubClassOf(owl:Thing ObjectHasValue(:r :a))
EquivalentClasses(:Q ObjectSomeValuesFrom(:r ObjectOneOf(:a)))"#),
    ("t_nom_value_range", true, r#"ObjectPropertyRange(:r ObjectOneOf(:a))
EquivalentClasses(:Q ObjectAllValuesFrom(:r ObjectOneOf(:a)))"#),
    ("t_obj_all", true, r#"ObjectPropertyRange(:r :C)
EquivalentClasses(:Q ObjectAllValuesFrom(:r :C))"#),
    ("t_obj_gci", true, r#"SubClassOf(owl:Thing ObjectSomeValuesFrom(:r :C))
EquivalentClasses(:Q ObjectSomeValuesFrom(:r owl:Thing))"#),
    ("t_obj_max", true, r#"FunctionalObjectProperty(:r)
EquivalentClasses(:Q ObjectMaxCardinality(1 :r))"#),
    ("t_obj_neg", true, r#"ObjectPropertyRange(:r :C)
EquivalentClasses(:Q ObjectComplementOf(ObjectSomeValuesFrom(:r ObjectComplementOf(:C))))"#),
];

/// `Some(rows)` for a published answer, `None` for a decline (exit 3).
fn classify(text: &str, route: Option<&str>) -> Option<BTreeSet<String>> {
    let path = std::env::temp_dir().join(format!(
        "km-top-bottom-{}-{}.ofn",
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
    command.env("KM_THREADS", "1");
    if let Some(route) = route {
        command.env("KM_ROUTE", route);
    }
    command
        .args(["classify", "--lines"])
        .arg(&path)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let started = Instant::now();
    let mut child = command.spawn().unwrap();
    let status = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break status;
        }
        if started.elapsed() > BOUND {
            let _ = child.kill();
            let _ = child.wait();
            let _ = std::fs::remove_file(&path);
            panic!("km classify exceeded {BOUND:?} on route {route:?}:\n{text}");
        }
        std::thread::sleep(Duration::from_millis(20));
    };
    let _ = std::fs::remove_file(&path);
    let mut stdout = String::new();
    child.stdout.take().unwrap().read_to_string(&mut stdout).unwrap();
    if status.code() == Some(3) {
        return None;
    }
    let mut stderr = String::new();
    child.stderr.take().unwrap().read_to_string(&mut stderr).unwrap();
    assert!(status.success(), "km failed on route {route:?}: {stderr}\n{stdout}");
    // A route may list the (trivial) subsumers of an unsatisfiable class.
    let rows: BTreeSet<String> = stdout.lines().filter(|l| !l.is_empty()).map(str::to_string).collect();
    let unsat: BTreeSet<String> = rows
        .iter()
        .filter_map(|row| row.strip_prefix("UNSAT\t").map(str::to_string))
        .collect();
    Some(
        rows.into_iter()
            .filter(|row| {
                !row.strip_prefix("SUB\t")
                    .and_then(|rest| rest.split('\t').next())
                    .is_some_and(|sub| unsat.contains(sub))
            })
            .collect(),
    )
}

#[test]
fn top_and_bottom_equivalent_classes_on_every_route() {
    let header = "Prefix(:=<http://ex.org/>)\nPrefix(owl:=<http://www.w3.org/2002/07/owl#>)\n\
                  Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\n\
                  Prefix(rdfs:=<http://www.w3.org/2000/01/rdf-schema#>)\nOntology(<http://ex.org/t>\n\
                  Declaration(Class(:A))\nDeclaration(Class(:B))\nDeclaration(Class(:C))\n\
                  Declaration(Class(:Q))\nDeclaration(DataProperty(:d))\n\
                  Declaration(ObjectProperty(:r))\nDeclaration(NamedIndividual(:a))\n\
                  Declaration(NamedIndividual(:b))\nSubClassOf(:A :B)\n";
    for (name, top, body) in CASES {
        let text = format!("{header}{body}\n)\n");
        let mut want: BTreeSet<String> =
            ["CONSISTENT 1", "DROPPED 0", "SUB\t:A\t:B"].iter().map(|s| s.to_string()).collect();
        if *top {
            for sub in ["A", "B", "C"] {
                want.insert(format!("SUB\t:{sub}\t:Q"));
            }
        } else {
            want.insert("UNSAT\t:Q".to_string());
        }
        for route in ROUTES {
            if let Some(rows) = classify(&text, *route) {
                assert_eq!(rows, want, "{name} on {route:?}");
            }
        }
    }
}
