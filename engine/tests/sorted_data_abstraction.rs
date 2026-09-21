//! CLI checks for the sorted data-node abstraction (`KM_SORTED_DATA=1`).
//! See docs/SORTED-DATA-ABSTRACTION.md.
use std::process::Command;

fn classify(source: &str, tag: &str, route: &str) -> Option<serde_json::Value> {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap()
        .join(".work/inputs/sorted-data-tests");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("{}-{tag}-{route}.ofn", std::process::id()));
    std::fs::write(&path, source).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_km"))
        .args(["classify", "--route", route])
        .arg(&path)
        .env("KM_SORTED_DATA", "1")
        .output()
        .unwrap();
    std::fs::remove_file(&path).unwrap();
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("unsupported"), "{route}: {stderr}");
        return None;
    }
    let text = String::from_utf8_lossy(&output.stdout);
    assert!(!text.contains("__km_obj") && !text.contains("__dt__"), "{route}: private name published");
    Some(serde_json::from_slice(&output.stdout).unwrap())
}

const PREFIXES: &str = "Prefix(owl:=<http://www.w3.org/2002/07/owl#>)\nPrefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\n";

/// The object domain is the single individual `a`, yet `a` may carry two data
/// values: data values are not objects, so `A` stays satisfiable.
#[test]
fn bounded_object_domain_does_not_bound_data_values() {
    let source = format!("{PREFIXES}Ontology(
Declaration(NamedIndividual(<http://e/a>)) Declaration(Class(<http://e/A>))
Declaration(DataProperty(<http://e/p>))
SubClassOf(<http://e/A> DataMinCardinality(2 <http://e/p>))
EquivalentClasses(owl:Thing ObjectOneOf(<http://e/a>)))");
    let mut answered = 0;
    for route in ["auto", "nominals", "production_all", "ht_general"] {
        let Some(result) = classify(&source, "bounded", route) else { continue };
        answered += 1;
        assert_eq!(result["consistent"], true, "{route}");
        assert_eq!(result["unsatisfiable"].as_array().unwrap().len(), 0, "{route}");
        assert_eq!(result["dropped"], 0, "{route}");
    }
    assert!(answered >= 2, "too few routes answered: {answered}");
}

/// A functional data property with two distinct asserted values is a genuine
/// clash, and an asserted value reaches the class that its restriction defines.
#[test]
fn data_assertions_take_part_in_reasoning() {
    let clash = format!("{PREFIXES}Ontology(
Declaration(NamedIndividual(<http://e/a>)) Declaration(DataProperty(<http://e/p>))
Declaration(Class(<http://e/A>))
SubClassOf(<http://e/A> DataMaxCardinality(1 <http://e/p>))
ClassAssertion(<http://e/A> <http://e/a>)
DataPropertyAssertion(<http://e/p> <http://e/a> \"1\"^^xsd:integer)
DataPropertyAssertion(<http://e/p> <http://e/a> \"2\"^^xsd:integer))");
    let control = clash.replace("\"2\"^^xsd:integer", "\"1\"^^xsd:integer");
    let mut answered = 0;
    for route in ["auto", "nominals", "ht_general"] {
        if let Some(result) = classify(&clash, "clash", route) {
            answered += 1;
            assert_eq!(result["consistent"], false, "{route}");
        }
        if let Some(result) = classify(&control, "control", route) {
            assert_eq!(result["consistent"], true, "{route}");
            assert_eq!(result["dropped"], 0, "{route}");
        }
    }
    assert!(answered >= 1, "no route answered the clash case");

    let derived = format!("{PREFIXES}Ontology(
Declaration(NamedIndividual(<http://e/a>)) Declaration(DataProperty(<http://e/p>))
Declaration(Class(<http://e/A>)) Declaration(Class(<http://e/B>)) Declaration(Class(<http://e/N>))
EquivalentClasses(<http://e/N> ObjectOneOf(<http://e/a>))
EquivalentClasses(<http://e/A> DataMinCardinality(1 <http://e/p>))
SubClassOf(<http://e/A> <http://e/B>)
DataPropertyAssertion(<http://e/p> <http://e/a> \"x\"))");
    let mut answered = 0;
    for route in ["auto", "nominals", "ht_general"] {
        let Some(result) = classify(&derived, "derived", route) else { continue };
        answered += 1;
        assert_eq!(result["consistent"], true, "{route}");
        assert_eq!(result["dropped"], 0, "{route}");
        let subs = result["subsumptions"].as_array().unwrap();
        let has = |a: &str, b: &str| subs.iter().any(|pair| pair[0] == a && pair[1] == b);
        assert!(has("http://e/N", "http://e/A"), "{route}: asserted value must make N ⊑ A");
        assert!(has("http://e/N", "http://e/B"), "{route}");
    }
    assert!(answered >= 1, "no route answered the derived case");
}
