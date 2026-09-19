use std::process::Command;

fn run(name: &str, source: &str) -> std::process::Output {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap()
        .join(".work/inputs/boolean-clash-tests");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("{}-{name}.ofn", std::process::id()));
    std::fs::write(&path, source).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_km"))
        .args(["classify", "--route", "auto"]).arg(&path).output().unwrap();
    std::fs::remove_file(path).unwrap();
    output
}

const BASE: &str = "DisjointClasses(<http://e/A> <http://e/B>)
    EquivalentClasses(<http://e/N> ObjectUnionOf(
        ObjectIntersectionOf(ObjectComplementOf(<http://e/P>) <http://e/T>) <http://e/B>))
    SubClassOf(<http://e/N> <http://e/A>) ClassAssertion(<http://e/B> <http://e/a>)";
const RULE: &str = "DLSafeRule(Body(DataPropertyAtom(<http://e/p> Variable(<http://e/x>)
    \"1\"^^<http://www.w3.org/2001/XMLSchema#integer>))
    Head(ClassAtom(<http://e/C> Variable(<http://e/x>))))";

#[test]
fn boolean_clash_precedes_unsupported_rules() {
    for rules in ["", RULE] {
        let output = run("clash", &format!("Ontology({BASE} {rules})"));
        assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
        let result: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(result["consistent"], false);
        assert_eq!(result["dropped"], 0);
    }
}

#[test]
fn boolean_controls_preserve_consistency_and_unsupported_rule_rejection() {
    for base in [BASE.replace("ObjectUnionOf", "ObjectIntersectionOf"),
        BASE.replace("EquivalentClasses", "SubClassOf")] {
        let output = run("control", &format!("Ontology({base})"));
        assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
        let result: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(result["consistent"], true);
        let rejected = run("unsupported-control", &format!("Ontology({base} {RULE})"));
        assert!(!rejected.status.success());
        assert!(String::from_utf8_lossy(&rejected.stderr).contains("DL-safe rules"));
    }
}
