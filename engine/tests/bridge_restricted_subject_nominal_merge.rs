//! Regression (fuzz `restricted_bug`): `{c, a} <= A0 <= {b}` forces
//! `a = b = c`, so `A5 <= {b, c}` entails `A5 <= A0`. With the bridge
//! restricted to the public subject `A5`, the first pair probe (`A5` vs `A1`)
//! merged the probe root into a nominal node. Model refutation read the
//! merged-away root label, which lacks `A0`, and dropped the entailed pair.
//! The probe model's root element is the merge representative.
use std::process::Command;

const SOURCE: &str = "Prefix(:=<http://f/>)
Ontology(<http://f/o>
Declaration(Class(:A0)) Declaration(Class(:A1)) Declaration(Class(:A2))
Declaration(Class(:A3)) Declaration(Class(:A4)) Declaration(Class(:A5))
Declaration(Class(:A6))
Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:s)) Declaration(ObjectProperty(:t))
Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b)) Declaration(NamedIndividual(:c))
SubClassOf(ObjectOneOf(:c :a) :A0)
SubClassOf(:A1 :A2)
SubClassOf(:A2 ObjectIntersectionOf(:A4 ObjectComplementOf(:A3)))
SubClassOf(:A4 ObjectMaxCardinality(1 ObjectInverseOf(:r)))
EquivalentClasses(:A1 ObjectComplementOf(:A6))
SubClassOf(:A3 ObjectMaxCardinality(1 :s))
SubClassOf(:A0 ObjectSomeValuesFrom(:s :A1))
SubClassOf(:A0 ObjectOneOf(:b))
SubObjectPropertyOf(:s :r)
SubClassOf(:A5 ObjectOneOf(:b :c))
)";

fn classify(subjects: Option<&str>) -> serde_json::Value {
    let dir = std::env::temp_dir().join(format!("km-bridge-restricted-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("rev.ofn");
    std::fs::write(&path, SOURCE).unwrap();
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars() {
        if key.starts_with("KM_") {
            command.env_remove(key);
        }
    }
    command
        .args(["classify"])
        .arg(&path)
        .env("KM_ROUTE", "ht_bridge")
        .env("KM_THREADS", "1")
        .env("KM_HT_DDB", "1")
        .env("KM_HT_NATIVE_FULL", "1")
        .env("KM_CACHE_CONFORMANCE", "1")
        .env("KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE", "1")
        .env("KM_FAST_IRI_GRAMMAR", "1");
    if let Some(subjects) = subjects {
        let file = dir.join("subjects.json");
        std::fs::write(&file, subjects).unwrap();
        command.env("KM_BRIDGE_PUBLIC_SUBJECT_FILE", &file);
    }
    let result = command.output().expect("run km classification");
    assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
    serde_json::from_slice(&result.stdout).unwrap()
}

fn has(answer: &serde_json::Value, sub: &str, sup: &str) -> bool {
    answer["subsumptions"]
        .as_array()
        .unwrap()
        .contains(&serde_json::json!([sub, sup]))
}

#[test]
fn restricted_bridge_subject_keeps_nominal_merge_subsumer() {
    let full = classify(None);
    assert!(has(&full, ":A5", ":A0"));
    for subjects in [r#"["A5"]"#, r#"["A5","A1"]"#] {
        let restricted = classify(Some(subjects));
        assert_eq!(restricted["consistent"], true, "{subjects}");
        assert!(
            has(&restricted, ":A5", ":A0"),
            "{subjects}: {restricted}"
        );
    }
}
