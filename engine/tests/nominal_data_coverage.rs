use std::process::Command;
use std::hash::{Hash, Hasher};

fn run(source: &str, route: &str) -> std::process::Output {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap()
        .join(".work/inputs/nominal-data-tests");
    std::fs::create_dir_all(&dir).unwrap();
    let mut hash = std::collections::hash_map::DefaultHasher::new();
    source.hash(&mut hash);
    let path = dir.join(format!("{}-{route}-{}.ofn", std::process::id(), hash.finish()));
    std::fs::write(&path, source).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_km"))
        .args(["classify", "--route", route]).arg(&path).output().unwrap();
    std::fs::remove_file(path).unwrap();
    output
}

#[test]
fn interacting_numeric_assertions_never_publish_incomplete_nominal_answers() {
    let source = r#"Ontology(
Declaration(Class(<http://e/A>)) Declaration(Class(<http://e/B>))
Declaration(NamedIndividual(<http://e/a>))
ClassAssertion(<http://e/A> <http://e/a>)
DataPropertyRange(<http://e/age> <http://www.w3.org/2001/XMLSchema#integer>)
DataPropertyAssertion(<http://e/age> <http://e/a> "-1"^^<http://www.w3.org/2001/XMLSchema#integer>)
SubClassOf(ObjectIntersectionOf(ObjectOneOf(<http://e/a>) <http://e/A>
 DataSomeValuesFrom(<http://e/age> DatatypeRestriction(<http://www.w3.org/2001/XMLSchema#integer>
 <http://www.w3.org/2001/XMLSchema#minExclusive> "0"^^<http://www.w3.org/2001/XMLSchema#integer>))) <http://e/B>)
DisjointClasses(<http://e/A> <http://e/B>))
"#;
    for route in ["auto", "nominals"] {
        let output = run(source, route);
        assert!(!output.status.success(), "{}", String::from_utf8_lossy(&output.stdout));
        assert!(output.stdout.is_empty());
        assert!(String::from_utf8_lossy(&output.stderr).contains("nominal data coverage"));
    }
    let source = r#"Ontology(
Declaration(Class(<http://e/A>)) Declaration(Class(<http://e/B>))
Declaration(NamedIndividual(<http://e/a>))
ClassAssertion(<http://e/A> <http://e/a>)
DataPropertyRange(<http://e/age> <http://www.w3.org/2001/XMLSchema#integer>)
DataPropertyAssertion(<http://e/age> <http://e/a> "5"^^<http://www.w3.org/2001/XMLSchema#integer>)
SubClassOf(ObjectIntersectionOf(ObjectOneOf(<http://e/a>) <http://e/A>
 DataSomeValuesFrom(<http://e/age> DatatypeRestriction(<http://www.w3.org/2001/XMLSchema#integer>
 <http://www.w3.org/2001/XMLSchema#minExclusive> "0"^^<http://www.w3.org/2001/XMLSchema#integer>))) <http://e/B>)
DisjointClasses(<http://e/A> <http://e/B>))
"#;
    for route in ["auto", "nominals"] {
        let output = run(source, route);
        assert!(!output.status.success(), "{}", String::from_utf8_lossy(&output.stdout));
        assert!(output.stdout.is_empty());
        assert!(String::from_utf8_lossy(&output.stderr).contains("nominal data coverage"));
    }
    let source = r#"Ontology(
Declaration(Class(<http://e/A>)) Declaration(Class(<http://e/B>))
Declaration(NamedIndividual(<http://e/a>))
ClassAssertion(<http://e/A> <http://e/a>)
DataPropertyRange(<http://e/age> <http://www.w3.org/2001/XMLSchema#integer>)
DataPropertyAssertion(<http://e/age> <http://e/a> "-1"^^<http://www.w3.org/2001/XMLSchema#integer>)
SubClassOf(ObjectIntersectionOf(ObjectOneOf(<http://e/a>) <http://e/A>
 DataSomeValuesFrom(<http://e/age> DatatypeRestriction(<http://www.w3.org/2001/XMLSchema#integer>
 <http://www.w3.org/2001/XMLSchema#minExclusive> "0"^^<http://www.w3.org/2001/XMLSchema#integer>))) <http://e/B>)
EquivalentClasses(<http://e/N> ObjectOneOf(<http://e/a>)))
"#;
    for route in ["auto", "nominals"] {
        let output = run(source, route);
        assert!(!output.status.success(), "{}", String::from_utf8_lossy(&output.stdout));
        assert!(output.stdout.is_empty());
        assert!(String::from_utf8_lossy(&output.stderr).contains("nominal data coverage"));
    }
    let source = r#"Ontology(
Declaration(Class(<http://e/A>)) Declaration(Class(<http://e/B>))
Declaration(NamedIndividual(<http://e/a>))
ClassAssertion(<http://e/A> <http://e/a>)
DataPropertyRange(<http://e/age> <http://www.w3.org/2001/XMLSchema#integer>)
DataPropertyAssertion(<http://e/age> <http://e/a> "5"^^<http://www.w3.org/2001/XMLSchema#integer>)
SubClassOf(ObjectIntersectionOf(ObjectOneOf(<http://e/a>) <http://e/A>
 DataSomeValuesFrom(<http://e/age> DatatypeRestriction(<http://www.w3.org/2001/XMLSchema#integer>
 <http://www.w3.org/2001/XMLSchema#minExclusive> "0"^^<http://www.w3.org/2001/XMLSchema#integer>))) <http://e/B>)
EquivalentClasses(<http://e/N> ObjectOneOf(<http://e/a>)))
"#;
    for route in ["auto", "nominals"] {
        let output = run(source, route);
        assert!(!output.status.success(), "{}", String::from_utf8_lossy(&output.stdout));
        assert!(output.stdout.is_empty());
        assert!(String::from_utf8_lossy(&output.stderr).contains("nominal data coverage"));
    }
}

#[test]
fn certified_redundant_data_and_proven_clashes_still_complete() {
    for (source, consistent) in [
        (r#"Ontology(ClassAssertion(<http://e/A> <http://e/a>)
          DataPropertyAssertion(<http://e/p> <http://e/a> "value"))"#, true),
        (r#"Ontology(ClassAssertion(<http://e/A> <http://e/a>)
          ClassAssertion(<http://e/B> <http://e/a>)
          DisjointClasses(<http://e/A> <http://e/B>)
          DataPropertyAssertion(<http://e/p> <http://e/a> "value")
          SubClassOf(DataHasValue(<http://e/p> "value") <http://e/C>))"#, false),
    ] {
        let output = run(source, "auto");
        assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
        let result: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(result["consistent"], consistent);
        assert_eq!(result["dropped"], 0);
    }
}
