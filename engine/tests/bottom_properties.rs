//! `owl:bottomObjectProperty` and `owl:bottomDataProperty` relate nothing
//! (OWL 2 Direct Semantics, Table 4). A class that requires a filler of
//! either builtin, or of one of its subproperties, is unsatisfiable.
use std::process::Command;

fn classify(text: &str, name: &str) -> String {
    let path = std::env::temp_dir().join(format!("km-bottom-{}-{name}.ofn", std::process::id()));
    std::fs::write(&path, text).unwrap();
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars_os() {
        if key.to_string_lossy().starts_with("KM_") {
            command.env_remove(key);
        }
    }
    let out = command.args(["classify", "--lines"]).arg(&path).output().unwrap();
    let _ = std::fs::remove_file(&path);
    assert!(out.status.success(), "{}", String::from_utf8_lossy(&out.stderr));
    String::from_utf8(out.stdout).unwrap()
}

fn unsat(out: &str, class: &str) -> bool {
    out.lines().any(|l| l == format!("UNSAT\t{class}"))
}

#[test]
fn fillers_of_bottom_object_property_are_unsatisfiable() {
    let out = classify(
        "Prefix(:=<http://x/o#>)\nOntology(<http://x/o>\n\
         Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C)) Declaration(Class(:D))\n\
         Declaration(ObjectProperty(:r))\n\
         SubClassOf(:A ObjectSomeValuesFrom(owl:bottomObjectProperty owl:Thing))\n\
         SubObjectPropertyOf(:r owl:bottomObjectProperty)\n\
         SubClassOf(:B ObjectMinCardinality(1 :r))\n\
         SubClassOf(:C ObjectSomeValuesFrom(ObjectInverseOf(owl:bottomObjectProperty) owl:Thing))\n\
         SubClassOf(:D ObjectAllValuesFrom(owl:bottomObjectProperty owl:Nothing))\n)",
        "object",
    );
    assert!(out.lines().any(|l| l == "CONSISTENT 1"), "{out}");
    for class in [":A", ":B", ":C"] {
        assert!(unsat(&out, class), "{class} should be unsatisfiable:\n{out}");
    }
    assert!(!unsat(&out, ":D"), "∀bottom.⊥ is ⊤:\n{out}");
}

#[test]
fn fillers_of_bottom_data_property_are_unsatisfiable() {
    let out = classify(
        "Prefix(:=<http://x/o#>)\nOntology(<http://x/o>\n\
         Declaration(Class(:A)) Declaration(Class(:B)) Declaration(DataProperty(:p))\n\
         SubClassOf(:A DataSomeValuesFrom(owl:bottomDataProperty rdfs:Literal))\n\
         SubDataPropertyOf(:p owl:bottomDataProperty)\n\
         SubClassOf(:B DataHasValue(:p \"1\"^^xsd:integer))\n)",
        "data",
    );
    assert!(out.lines().any(|l| l == "CONSISTENT 1"), "{out}");
    for class in [":A", ":B"] {
        assert!(unsat(&out, class), "{class} should be unsatisfiable:\n{out}");
    }
}
