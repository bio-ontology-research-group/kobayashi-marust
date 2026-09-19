use std::process::Command;

fn classify(name: &str, source: &str) -> serde_json::Value {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap()
        .join(".work/inputs/atomic-object-tests");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("{}-{name}.ofn", std::process::id()));
    std::fs::write(&path, source).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_km"))
        .args(["classify", "--route", "auto"]).arg(&path).output().unwrap();
    std::fs::remove_file(path).unwrap();
    assert!(output.status.success(), "{name}: {}", String::from_utf8_lossy(&output.stderr));
    let result: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(result["dropped"], 0);
    result
}

#[test]
fn disjoint_individual_class_witnesses_can_use_separate_models() {
    let result = classify("separate", "Ontology(
        Declaration(Class(<http://e/A>)) Declaration(Class(<http://e/B>))
        DisjointClasses(<http://e/A> <http://e/B>)
        SubClassOf(<http://e/A> ObjectAllValuesFrom(<http://e/r> <http://e/B>))
        FunctionalObjectProperty(<http://e/r>) InverseFunctionalObjectProperty(<http://e/r>)
        ClassAssertion(<http://e/A> <http://e/a>) ClassAssertion(<http://e/B> <http://e/b>))");
    assert_eq!(result["consistent"], true);
    assert_eq!(result["unsatisfiable"], serde_json::json!([]));
}

#[test]
fn non_el_unsatisfiable_asserted_class_makes_whole_ontology_inconsistent() {
    let tbox = "SubClassOf(<http://e/A> ObjectSomeValuesFrom(<http://e/r> <http://e/B>))
        SubClassOf(<http://e/A> ObjectAllValuesFrom(<http://e/r> <http://e/C>))
        DisjointClasses(<http://e/B> <http://e/C>) FunctionalObjectProperty(<http://e/r>)";
    let without = classify("tbox", &format!("Ontology({tbox})"));
    assert_eq!(without["consistent"], true);
    assert!(without["unsatisfiable"].as_array().unwrap().contains(&serde_json::json!("http://e/A")));
    let with = classify("asserted", &format!("Ontology({tbox} ClassAssertion(<http://e/A> <http://e/a>))"));
    assert_eq!(with["consistent"], false);
}

#[test]
fn anonymous_atomic_witnesses_preserve_consistency_and_shared_identity() {
    for (second, consistent) in [("_:b", true), ("<http://e/a>", true), ("_:a", false)] {
        let source = format!("Ontology(
            DisjointClasses(<http://e/A> <http://e/B>)
            SubClassOf(<http://e/A> ObjectAllValuesFrom(<http://e/r> <http://e/B>))
            ClassAssertion(<http://e/A> _:a) ClassAssertion(<http://e/B> {second}))");
        let result = classify("anonymous", &source);
        assert_eq!(result["consistent"], consistent, "{second}");
    }
    let result = classify("anonymous-unsat", "Ontology(
        SubClassOf(<http://e/A> ObjectSomeValuesFrom(<http://e/r> <http://e/B>))
        SubClassOf(<http://e/A> ObjectAllValuesFrom(<http://e/r> <http://e/C>))
        DisjointClasses(<http://e/B> <http://e/C>)
        ClassAssertion(<http://e/A> _:a) ClassAssertion(<http://e/B> _:b))");
    assert_eq!(result["consistent"], false);
}

#[test]
fn two_classes_on_one_individual_cannot_use_separate_witnesses() {
    let result = classify("joint", "Ontology(
        DisjointClasses(<http://e/A> <http://e/B>)
        SubClassOf(<http://e/A> ObjectAllValuesFrom(<http://e/r> <http://e/B>))
        ClassAssertion(<http://e/A> <http://e/a>) ClassAssertion(<http://e/B> <http://e/a>))");
    assert_eq!(result["consistent"], false);
}
