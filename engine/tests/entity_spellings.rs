//! One IRI written in several spellings names one entity (Protégé plugin
//! bug 5 and its two-prefix variant). Each case is entailed only when the
//! spellings are identified, so a missing row is a wrong answer.
use std::process::Command;

fn classify(text: &str, name: &str) -> String {
    let path = std::env::temp_dir().join(format!("km-spellings-{}-{name}.ofn", std::process::id()));
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

#[test]
fn two_prefixes_for_one_namespace_name_one_class() {
    let out = classify(
        "Prefix(p:=<http://x/o#>)\nPrefix(q:=<http://x/o#>)\nOntology(<http://x/o>\n\
         Declaration(Class(p:A)) Declaration(Class(p:C)) Declaration(Class(q:D))\n\
         SubClassOf(p:A p:C)\nSubClassOf(q:C q:D)\n)",
        "two-prefixes",
    );
    assert!(out.lines().any(|l| l == "SUB\tp:A\tq:D"), "{out}");
}

#[test]
fn full_and_prefixed_class_spellings_name_one_class() {
    let out = classify(
        "Prefix(:=<http://x/o#>)\nOntology(<http://x/o>\n\
         Declaration(Class(:A)) Declaration(Class(:C)) Declaration(Class(:D))\n\
         SubClassOf(:A <http://x/o#C>)\nSubClassOf(:C :D)\n)",
        "full-prefixed",
    );
    assert!(out.lines().any(|l| l == "SUB\t:A\t:D"), "{out}");
}

#[test]
fn mixed_individual_spellings_name_one_individual() {
    let out = classify(
        "Prefix(p:=<http://x/o#>)\nPrefix(q:=<http://x/o#>)\nOntology(<http://x/o>\n\
         Declaration(Class(p:C)) Declaration(NamedIndividual(p:a))\n\
         ClassAssertion(p:C <http://x/o#a>)\nClassAssertion(ObjectComplementOf(p:C) q:a)\n)",
        "individuals",
    );
    assert!(out.lines().any(|l| l == "CONSISTENT 0"), "{out}");
}
