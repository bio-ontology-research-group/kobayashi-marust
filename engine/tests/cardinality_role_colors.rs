use std::process::Command;

#[test]
fn shared_successors_have_parent_specific_colors() {
    let directory = std::env::temp_dir().join(format!("km-shared-colors-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    let input = directory.join("shared.ofn");
    let iri = |name: &str| format!("<http://km.test/shared#{name}>");
    let mut source = format!("Ontology(Declaration(Class({})) SubClassOf({} ObjectExactCardinality(3 {} {}))\n", iri("Counted"), iri("Counted"), iri("r"), iri("F"));
    source.push_str(&format!("Declaration(Class({})) Declaration(ObjectProperty({}))\n", iri("F"), iri("r")));
    let successors = ["a", "b", "c", "d"];
    source.push_str(&format!("DifferentIndividuals({})\n", successors.iter().map(|s| iri(s)).collect::<Vec<_>>().join(" ")));
    for successor in successors { source.push_str(&format!("ClassAssertion({} {})\n", iri("F"), iri(successor))); }
    // Each triple of four distinct successors has its own root. A global
    // three-color assignment cannot work, whereas parent-indexed labels can.
    for excluded in 0..4 {
        let root = iri(&format!("root{excluded}"));
        source.push_str(&format!("ClassAssertion({} {root})\n", iri("Counted")));
        for (index, successor) in successors.iter().enumerate() {
            if index != excluded { source.push_str(&format!("ObjectPropertyAssertion({} {root} {})\n", iri("r"), iri(successor))); }
        }
    }
    source.push(')');
    std::fs::write(&input, source).unwrap();
    let mut outputs = Vec::new();
    for colored in [false, true] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
        command.env_remove("KM_CARDINALITY_COLORS").env("KM_NO_HT_CARD", "1")
            .env("KM_NO_RETRY", "1").env("KM_CENTRAL_TIME_CAP", "30");
        if colored { command.env("KM_CARDINALITY_COLORS", "1"); }
        let result = command.args(["classify", "--route", "nominals"]).arg(&input).output().unwrap();
        assert!(result.status.success(), "colored={colored}: {}", String::from_utf8_lossy(&result.stderr));
        let value: serde_json::Value = serde_json::from_slice(&result.stdout).unwrap();
        assert_eq!(value["consistent"], true, "{value}");
        assert_eq!(value["dropped"], 0, "{value}");
        outputs.push(value);
    }
    assert_eq!(outputs[0], outputs[1]);
    std::fs::remove_dir_all(directory).unwrap();
}

#[test]
fn colored_bounds_preserve_ordinary_classification() {
    let directory = std::env::temp_dir().join(format!("km-role-colors-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    let input = directory.join("bounds.ofn");
    std::fs::write(&input, r#"Ontology(
Declaration(ObjectProperty(<http://km.test/colors#r>)) Declaration(Class(<http://km.test/colors#F>))
Declaration(Class(<http://km.test/colors#A>))
Declaration(Class(<http://km.test/colors#B>))
Declaration(Class(<http://km.test/colors#C>))
Declaration(Class(<http://km.test/colors#D>))
Declaration(Class(<http://km.test/colors#E>))
Declaration(Class(<http://km.test/colors#Z>))
EquivalentClasses(<http://km.test/colors#A> ObjectMinCardinality(2 <http://km.test/colors#r> <http://km.test/colors#F>))
EquivalentClasses(<http://km.test/colors#B> ObjectMaxCardinality(1 <http://km.test/colors#r> <http://km.test/colors#F>))
EquivalentClasses(<http://km.test/colors#C> ObjectIntersectionOf(<http://km.test/colors#A> <http://km.test/colors#B>))
EquivalentClasses(<http://km.test/colors#D> ObjectIntersectionOf(<http://km.test/colors#A> ObjectComplementOf(<http://km.test/colors#A>)))
EquivalentClasses(<http://km.test/colors#E> ObjectIntersectionOf(ObjectMinCardinality(1 <http://km.test/colors#r> <http://km.test/colors#F>) <http://km.test/colors#B>))
EquivalentClasses(<http://km.test/colors#Z> ObjectMaxCardinality(0 <http://km.test/colors#r> <http://km.test/colors#F>))
SubClassOf(<http://km.test/colors#Z> <http://km.test/colors#B>)
)"#).unwrap();
    let mut outputs = Vec::new();
    for colored in [false, true] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
        command.env_remove("KM_CARDINALITY_COLORS").env("KM_NO_HT_CARD", "1")
            .env("KM_NO_RETRY", "1").env("KM_CENTRAL_TIME_CAP", "30");
        if colored { command.env("KM_CARDINALITY_COLORS", "1"); }
        let result = command.args(["classify", "--route", "cb_plain1"]).arg(&input).output().unwrap();
        assert!(result.status.success(), "colored={colored}: {}", String::from_utf8_lossy(&result.stderr));
        let value: serde_json::Value = serde_json::from_slice(&result.stdout).unwrap();
        assert_eq!(value["consistent"], true, "{value}");
        assert_eq!(value["dropped"], 0, "{value}");
        let unsat = value["unsatisfiable"].as_array().unwrap();
        for name in ["C", "D"] { assert!(unsat.contains(&serde_json::json!(format!("http://km.test/colors#{name}"))), "{value}"); }
        for name in ["A", "B", "E", "Z"] { assert!(!unsat.contains(&serde_json::json!(format!("http://km.test/colors#{name}"))), "{value}"); }
        outputs.push(value);
    }
    assert_eq!(outputs[0], outputs[1]);
    std::fs::remove_dir_all(directory).unwrap();
}

#[test]
fn colored_larger_minimum_and_maximum_clash() {
    let directory = std::env::temp_dir().join(format!("km-large-role-colors-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    let input = directory.join("clash.ofn");
    std::fs::write(&input, r#"Ontology(
Declaration(Class(<http://km.test/colors#C>))
Declaration(Class(<http://km.test/colors#F>)) Declaration(ObjectProperty(<http://km.test/colors#r>))
SubClassOf(<http://km.test/colors#C> ObjectMinCardinality(3 <http://km.test/colors#r> <http://km.test/colors#F>))
SubClassOf(<http://km.test/colors#C> ObjectMaxCardinality(2 <http://km.test/colors#r> <http://km.test/colors#F>))
)"#).unwrap();
    let mut outputs = Vec::new();
    for colored in [false, true] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
        command.env_remove("KM_CARDINALITY_COLORS").env("KM_NO_HT_CARD", "1")
            .env("KM_NO_RETRY", "1").env("KM_CENTRAL_TIME_CAP", "30");
        if colored { command.env("KM_CARDINALITY_COLORS", "1"); }
        let result = command.args(["classify", "--route", "cb_plain1"]).arg(&input).output().unwrap();
        assert!(result.status.success(), "colored={colored}: {}", String::from_utf8_lossy(&result.stderr));
        let value: serde_json::Value = serde_json::from_slice(&result.stdout).unwrap();
        assert_eq!(value["consistent"], true, "{value}");
        assert_eq!(value["dropped"], 0, "{value}");
        assert!(value["unsatisfiable"].as_array().unwrap().contains(&serde_json::json!("http://km.test/colors#C")), "{value}");
        outputs.push(value);
    }
    assert_eq!(outputs[0], outputs[1]);
    std::fs::remove_dir_all(directory).unwrap();
}
