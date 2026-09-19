use std::process::Command;
#[test]
fn existing_individual_restrictions_participate_in_consistency() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap()
        .join(".work/inputs/general-ht-abox-tests");
    std::fs::create_dir_all(&dir).unwrap();
    {
        let source = r#"Ontology(
Declaration(Class(<http://e/A>)) Declaration(Class(<http://e/B>))
Declaration(NamedIndividual(<http://e/a>))
ClassAssertion(<http://e/A> <http://e/a>)
DataPropertyRange(<http://e/age> <http://www.w3.org/2001/XMLSchema#integer>)
ClassAssertion(DataHasValue(<http://e/age> "-1"^^<http://www.w3.org/2001/XMLSchema#integer>) <http://e/a>)
SubClassOf(ObjectIntersectionOf(ObjectOneOf(<http://e/a>) <http://e/A>
 DataSomeValuesFrom(<http://e/age> DatatypeRestriction(<http://www.w3.org/2001/XMLSchema#integer>
 <http://www.w3.org/2001/XMLSchema#minExclusive> "0"^^<http://www.w3.org/2001/XMLSchema#integer>))) <http://e/B>)
DisjointClasses(<http://e/A> <http://e/B>))
"#;
        let path = dir.join(format!("{}-clash-negative.ofn", std::process::id()));
        std::fs::write(&path, source).unwrap();
        for route in ["auto", "ht_general"] {
        for isolated in [false, true] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
        command.args(["classify", "--route", route]).arg(&path);
        if isolated { command.env("KM_NO_INPROC_HT", "1"); }
        let output = command.output().unwrap();

        assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
        let result: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(result["consistent"], true);
        assert_eq!(result["dropped"], 0);
        assert!(!String::from_utf8_lossy(&output.stdout).contains("__nom__"));
        }
        }
        std::fs::remove_file(path).unwrap();
    }
    {
        let source = r#"Ontology(
Declaration(Class(<http://e/A>)) Declaration(Class(<http://e/B>))
Declaration(NamedIndividual(<http://e/a>))
ClassAssertion(<http://e/A> <http://e/a>)
DataPropertyRange(<http://e/age> <http://www.w3.org/2001/XMLSchema#integer>)
ClassAssertion(DataHasValue(<http://e/age> "5"^^<http://www.w3.org/2001/XMLSchema#integer>) <http://e/a>)
SubClassOf(ObjectIntersectionOf(ObjectOneOf(<http://e/a>) <http://e/A>
 DataSomeValuesFrom(<http://e/age> DatatypeRestriction(<http://www.w3.org/2001/XMLSchema#integer>
 <http://www.w3.org/2001/XMLSchema#minExclusive> "0"^^<http://www.w3.org/2001/XMLSchema#integer>))) <http://e/B>)
DisjointClasses(<http://e/A> <http://e/B>))
"#;
        let path = dir.join(format!("{}-clash-positive.ofn", std::process::id()));
        std::fs::write(&path, source).unwrap();
        for route in ["auto", "ht_general"] {
        for isolated in [false, true] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
        command.args(["classify", "--route", route]).arg(&path);
        if isolated { command.env("KM_NO_INPROC_HT", "1"); }
        let output = command.output().unwrap();

        assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
        let result: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(result["consistent"], false);
        assert_eq!(result["dropped"], 0);
        assert!(!String::from_utf8_lossy(&output.stdout).contains("__nom__"));
        }
        }
        std::fs::remove_file(path).unwrap();
    }
    {
        let source = r#"Ontology(
Declaration(Class(<http://e/A>)) Declaration(Class(<http://e/B>))
Declaration(NamedIndividual(<http://e/a>))
ClassAssertion(<http://e/A> <http://e/a>)
DataPropertyRange(<http://e/age> <http://www.w3.org/2001/XMLSchema#integer>)
ClassAssertion(DataHasValue(<http://e/age> "-1"^^<http://www.w3.org/2001/XMLSchema#integer>) <http://e/a>)
SubClassOf(ObjectIntersectionOf(ObjectOneOf(<http://e/a>) <http://e/A>
 DataSomeValuesFrom(<http://e/age> DatatypeRestriction(<http://www.w3.org/2001/XMLSchema#integer>
 <http://www.w3.org/2001/XMLSchema#minExclusive> "0"^^<http://www.w3.org/2001/XMLSchema#integer>))) <http://e/B>)
EquivalentClasses(<http://e/N> ObjectOneOf(<http://e/a>)))
"#;
        let path = dir.join(format!("{}-nominal-query-negative.ofn", std::process::id()));
        std::fs::write(&path, source).unwrap();
        for route in ["auto", "ht_general"] {
        for isolated in [false, true] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
        command.args(["classify", "--route", route]).arg(&path);
        if isolated { command.env("KM_NO_INPROC_HT", "1"); }
        let output = command.output().unwrap();

        assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
        let result: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(result["consistent"], true);
        assert_eq!(result["dropped"], 0);
        assert!(!String::from_utf8_lossy(&output.stdout).contains("__nom__"));
        let has_b = result["subsumptions"].as_array().unwrap().contains(&serde_json::json!(["http://e/N", "http://e/B"]));
        assert_eq!(has_b, false);
        }
        }
        std::fs::remove_file(path).unwrap();
    }
    {
        let source = r#"Ontology(
Declaration(Class(<http://e/A>)) Declaration(Class(<http://e/B>))
Declaration(NamedIndividual(<http://e/a>))
ClassAssertion(<http://e/A> <http://e/a>)
DataPropertyRange(<http://e/age> <http://www.w3.org/2001/XMLSchema#integer>)
ClassAssertion(DataHasValue(<http://e/age> "5"^^<http://www.w3.org/2001/XMLSchema#integer>) <http://e/a>)
SubClassOf(ObjectIntersectionOf(ObjectOneOf(<http://e/a>) <http://e/A>
 DataSomeValuesFrom(<http://e/age> DatatypeRestriction(<http://www.w3.org/2001/XMLSchema#integer>
 <http://www.w3.org/2001/XMLSchema#minExclusive> "0"^^<http://www.w3.org/2001/XMLSchema#integer>))) <http://e/B>)
EquivalentClasses(<http://e/N> ObjectOneOf(<http://e/a>)))
"#;
        let path = dir.join(format!("{}-nominal-query-positive.ofn", std::process::id()));
        std::fs::write(&path, source).unwrap();
        for route in ["auto", "ht_general"] {
        for isolated in [false, true] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
        command.args(["classify", "--route", route]).arg(&path);
        if isolated { command.env("KM_NO_INPROC_HT", "1"); }
        let output = command.output().unwrap();

        assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
        let result: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(result["consistent"], true);
        assert_eq!(result["dropped"], 0);
        assert!(!String::from_utf8_lossy(&output.stdout).contains("__nom__"));
        let has_b = result["subsumptions"].as_array().unwrap().contains(&serde_json::json!(["http://e/N", "http://e/B"]));
        assert_eq!(has_b, true);
        }
        }
        std::fs::remove_file(path).unwrap();
    }
}
