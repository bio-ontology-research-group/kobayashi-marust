//! VALUE rows between named individuals whose role path runs through an
//! anonymous individual (Protégé parity run 3, `h_f9002_44_chain_anon`).
//!
//! Each case states the rows HermiT 1.4.3 entails (`isEntailed` of the
//! property assertion). `km classify --lines --values` and the realization
//! path must print exactly those VALUE rows.

use std::collections::BTreeSet;
use std::path::PathBuf;
use std::process::Command;

const P: &str = "Prefix(:=<http://ex.org/>)\nPrefix(owl:=<http://www.w3.org/2002/07/owl#>)\n";

/// (name, axioms, entailed VALUE rows as `r a b`).
const CASES: &[(&str, &str, &[&str])] = &[
    (
        // B(a4), B ⊑ ∃s3⁻.B, s3⁻ ⊑ s1, s1 symmetric, s1 ∘ s3 ⊑ c1: the chain
        // leaves a4 into its anonymous s3⁻-successor and returns.
        "chain_anon",
        "Declaration(NamedIndividual(:a4)) Declaration(Class(:B))\n\
         Declaration(ObjectProperty(:s1)) Declaration(ObjectProperty(:s3)) Declaration(ObjectProperty(:c1))\n\
         SubObjectPropertyOf(ObjectInverseOf(:s3) :s1) SymmetricObjectProperty(:s1)\n\
         SubClassOf(:B ObjectSomeValuesFrom(ObjectInverseOf(:s3) :B))\n\
         SubObjectPropertyOf(ObjectPropertyChain(:s1 :s3) :c1) ClassAssertion(:B :a4)",
        &["c1 a4 a4"],
    ),
    (
        // A symmetric transitive t with an anonymous successor loops back.
        "transitive_symmetric_loop",
        "Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b)) Declaration(Class(:B))\n\
         Declaration(ObjectProperty(:t)) Declaration(ObjectProperty(:k))\n\
         TransitiveObjectProperty(:t) SymmetricObjectProperty(:t)\n\
         SubClassOf(:B ObjectSomeValuesFrom(:t owl:Thing)) ClassAssertion(:B :a)\n\
         ObjectPropertyAssertion(:k :b :b)",
        &["k b b", "t a a"],
    ),
    (
        // The s-successor of x merges with b: s ⊑ f, f functional, f(x, b).
        "functional_merge_with_named",
        "Declaration(NamedIndividual(:x)) Declaration(NamedIndividual(:b)) Declaration(Class(:C))\n\
         Declaration(ObjectProperty(:s)) Declaration(ObjectProperty(:f))\n\
         SubObjectPropertyOf(:s :f) FunctionalObjectProperty(:f)\n\
         ObjectPropertyAssertion(:f :x :b) ClassAssertion(ObjectSomeValuesFrom(:s :C) :x)",
        &["f x b", "s x b"],
    ),
];

fn write_case(name: &str, axioms: &str) -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("values_through_anonymous");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("{name}.ofn"));
    std::fs::write(&path, format!("{P}Ontology(<http://ex.org/{name}>\n{axioms}\n)\n")).unwrap();
    path
}

fn values(path: &PathBuf, options: &[&str]) -> BTreeSet<String> {
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars() {
        if key.starts_with("KM_") {
            command.env_remove(key);
        }
    }
    command.env("KM_THREADS", "1").arg("classify").arg("--lines").args(options).arg(path);
    let out = command.output().unwrap();
    assert!(out.status.success(), "km failed on {}: {}", path.display(), String::from_utf8_lossy(&out.stderr));
    String::from_utf8(out.stdout)
        .unwrap()
        .lines()
        .filter_map(|l| l.strip_prefix("VALUE\t"))
        .map(|l| l.split('\t').map(|t| t.trim_start_matches(':')).collect::<Vec<_>>().join(" "))
        .collect()
}

#[test]
fn value_rows_through_anonymous_individuals_match_hermit() {
    for (name, axioms, expected) in CASES {
        let path = write_case(name, axioms);
        let expected: BTreeSet<String> = expected.iter().map(|s| s.to_string()).collect();
        for options in [&["--values"][..], &["--realize", "--values"], &["--realize", "--values", "--different"]] {
            assert_eq!(values(&path, options), expected, "{name} {options:?}");
        }
    }
}
