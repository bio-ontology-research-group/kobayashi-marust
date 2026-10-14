//! A structurally triggered antecedent reuses the existential definer of a
//! positive occurrence; its reified And filler must also be recognised.
//! A0 ⊑ ∃s.A7, A7 ⊑ A5 ⊑ A1 and A8 ≡ ∃s.(A1 ⊓ A5) entail A0 ⊑ A8.

const SOURCE: &str = "Prefix(:=<http://f/>)
Ontology(<http://f/o>
Declaration(Class(:A0)) Declaration(Class(:A1)) Declaration(Class(:A5))
Declaration(Class(:A7)) Declaration(Class(:A8)) Declaration(ObjectProperty(:s))
SubClassOf(:A5 :A1)
SubClassOf(:A7 :A5)
SubClassOf(:A0 ObjectSomeValuesFrom(:s :A7))
EquivalentClasses(:A8 ObjectSomeValuesFrom(:s ObjectIntersectionOf(:A1 :A5)))
)";

#[test]
fn triggered_existential_with_and_filler_is_complete() {
    let dir = std::env::temp_dir().join(format!("km-trigger-filler-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("min2.ofn");
    std::fs::write(&path, SOURCE).unwrap();
    for route in ["auto", "production_all", "elc"] {
        let output = std::process::Command::new(env!("CARGO_BIN_EXE_km"))
            .args(["classify", "--route", route])
            .arg(&path)
            .output()
            .unwrap();
        assert!(output.status.success(), "route {route}: {}", String::from_utf8_lossy(&output.stderr));
        let stdout = String::from_utf8(output.stdout).unwrap();
        assert!(stdout.contains(r#"[":A0", ":A8"]"#), "route {route} misses A0 ⊑ A8: {stdout}");
    }
    std::fs::remove_dir_all(&dir).ok();
}
